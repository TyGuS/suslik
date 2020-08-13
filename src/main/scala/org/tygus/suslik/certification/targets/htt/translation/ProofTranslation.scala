package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.htt.logic.Proof._
import org.tygus.suslik.certification.targets.htt.logic.ProofProducers._
import org.tygus.suslik.certification.targets.htt.logic.ProofSteps._
import org.tygus.suslik.certification.targets.htt.translation.Translation._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.synthesis._

object ProofTranslation {
  private case class TraversalItem(node: CertTree.Node, cenv: CEnvironment)

  def translate(node: CertTree.Node, cenv: CEnvironment): Proof = {
    val initialGoal = translateGoal(node.goal)
    val traversalItem = TraversalItem(node, cenv)
    val initialKont = PrependProofProducer(GhostElimStep(initialGoal))
    val (proofBody, _) = traverseProof(traversalItem, initialKont)
    Proof(proofBody, initialGoal.programVars)
  }

  def traverseProof(item: TraversalItem, kont: ProofProducer): KontResult = {
    def translateOperation(s: Statement, cenv: CEnvironment): KontResult = s match {
      case Skip =>
        val goal = cenv.initialGoal.subst(cenv.ghostSubst)
        val post = goal.post.subst(cenv.subst)
        val postEx = goal.existentials.map(_.subst(cenv.subst))
        val unfoldings = cenv.unfoldings.map { case (app, c) => app.subst(cenv.subst) -> c.subst(cenv.subst) }
        (EmpStep(post, postEx, unfoldings), cenv)
      case Load(to, _, from, _) =>
        (ReadStep(translateVar(to), translateVar(from)), cenv)
      case Store(to, offset, e) =>
        val frame = item.node.goal.callGoal.isEmpty
        (WriteStep(translateVar(to), offset, translateExpr(e), frame), cenv)
      case Malloc(to, tpe, sz) =>
        (AllocStep(translateVar(to), translateType(tpe), sz), cenv)
      case Free(v) =>
        val block = item.node.footprint.pre.sigma.blocks.find(_.loc == v)
        assert(block.nonEmpty)
        (FreeStep(block.get.sz), cenv)
      case Call(_, _, _) =>
        assert(item.node.goal.callGoal.isDefined)
        val callGoal = item.node.goal.callGoal.get

        // create call step
        val companionToFresh = callGoal.companionToFresh.map{ case (k, v) => translateVar(k) -> translateVar(v)}
        val freshToActual = callGoal.freshToActual.map{ case (k, v) => translateVar(k) -> translateExpr(v)}
        val cgoal = cenv.initialGoal.subst(companionToFresh).subst(freshToActual)

        (CallStep(cgoal, freshCallId), cenv)
      case _ => throw TranslationException("Operation not supported")
    }

    def translateProducer(stmtProducer: StmtProducer, cenv: CEnvironment): (ProofProducer, CEnvironment) = {
      stmtProducer match {
        case ChainedProducer(p1, p2) =>
          val (k1, cenv1) = translateProducer(p1, cenv)
          val (k2, cenv2) = translateProducer(p2, cenv1)
          (k1 >> k2, cenv2)
        case PartiallyAppliedProducer(p, _) =>
          translateProducer(p, cenv)
        case SubstProducer(subst) =>
          val csub = subst.map { case (v, e) => translateVar(v) -> translateExpr(e).subst(cenv.ghostSubst) }
          val cenv1 = cenv.copy(subst = cenv.subst ++ csub)
          (IdProofProducer, cenv1)
        case GhostSubstProducer(ghostSubst) =>
          val newGhostSubst = ghostSubst.map { case (v, e) => translateVar(v) -> translateVar(e) }
          val newSubst = cenv.subst.map { case (v, e) => v.substVar(newGhostSubst) -> e.subst(newGhostSubst)}
          val newUnfoldings = cenv.unfoldings.map { case (app, e) => app.subst(newGhostSubst) -> e.subst(newGhostSubst) }
          val cenv1 = cenv.copy(subst = newSubst, ghostSubst = cenv.ghostSubst ++ newGhostSubst, unfoldings = newUnfoldings)
          (IdProofProducer, cenv1)
        case UnfoldProducer(app, selector, substPred, substEx, substArgs) =>
          val cselector = translateExpr(selector)
          val capp = translateSApp(app)
          val csubPred = substPred.map { case (src, dst) => translateVar(src) -> translateVar(dst) }
          val csubEx = substEx.map { case (src, dst) => translateVar(src) -> translateVar(dst) }
          val csubArgs = substArgs.map { case (src, dst) => translateVar(src) -> translateExpr(dst) }

          // get clause with substitutions
          val predicate = cenv.predicates(app.pred)
          val cclause = predicate.clauses.find(_.selector == cselector).get
          val actualClause = cclause.subst(csubPred).subst(csubEx).subst(csubArgs).subst(cenv.ghostSubst)
          val cenv1 = cenv.copy(unfoldings = cenv.unfoldings ++ Map(capp -> actualClause))
          (IdProofProducer, cenv1)
        case ConstProducer(s) =>
          val (step, cenv1) = translateOperation(s, cenv)
          (ConstProofProducer(step, cenv1), cenv1)
        case PrependProducer(s) =>
          val (step, cenv1) = translateOperation(s, cenv)
          (PrependProofProducer(step), cenv1)
        case BranchProducer(_) =>
          val sapp = translateSApp(item.node.footprint.pre.sigma.apps.head)
          val pred = cenv.predicates(sapp.pred)
          val subgoals = item.node.children.map(n => translateGoal(n.goal))
          val initialSub: SubstVar = Map.empty
          val sub = pred.clauses.zip(subgoals).foldLeft(initialSub){ case (acc, (c, g)) => acc ++ g.pre.sigma.unify(c.asn.sigma) }
          val actualPred = pred.subst(sub)
          val openPostSteps = actualPred.clauses.map(c => OpenPostStep(sapp, c.asn, c.existentials))
          (BranchProofProducer(openPostSteps, cenv), cenv)
        case GuardedProducer(_, _) =>
          (GuardedProofProducer(cenv), cenv)
        case _ =>
          (IdProofProducer, cenv)
      }
    }

    def generateNextItems(p: ProofProducer, cenv: CEnvironment): Seq[TraversalItem] = {
      item.node.children.map(node => TraversalItem(node, cenv))
    }

    // If at a branching point, queue up the traversal of each branch as nested calls of `traverseProof` in the continuation
    def updateProducerPost(nextItems: Seq[TraversalItem], nextKont: ProofProducer, cenv: CEnvironment): ProofProducer = nextKont match {
      case _: Branching =>
        nextItems.tail.foldLeft(nextKont >> kont) {
          case (foldedP, item) => FoldProofProducer(traverseProof, item, foldedP)
        }
      case _ =>
        nextKont >> kont
    }

    val (p0, cenv1) = translateProducer(item.node.kont, item.cenv)
    val p = p0.simplify
    val nextItems = generateNextItems(p, cenv1)
    val nextKont = updateProducerPost(nextItems, p, cenv1).simplify

      nextItems.headOption match {
      case Some(childHead) =>
        traverseProof(childHead, nextKont)
      case None =>
        nextKont(Nil)
    }
  }
}
