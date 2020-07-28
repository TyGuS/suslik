package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.Proof._
import org.tygus.suslik.certification.targets.htt.logic.ProofProducers._
import org.tygus.suslik.certification.targets.htt.logic.ProofSteps._
import org.tygus.suslik.certification.targets.htt.translation.Translation._
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Block
import org.tygus.suslik.synthesis._

object ProofTranslation {
  private case class TraversalItem(node: CertTree.Node, cenv: CEnvironment) extends Traversable

  def translate(node: CertTree.Node, proc: Procedure, goal: CGoal, cenv: CEnvironment): Proof = {
    val traversalItem = TraversalItem(node, cenv)
    val proofBody = traverseProof(traversalItem, PrependProofProducer(GhostElimStep(goal)))
    val inductive = proc.body.vars.contains(Var(proc.name))
    Proof(proofBody, goal.programVars, inductive)
  }

  def traverseProof(item: TraversalItem, kont: ProofProducer): ProofStep = {
    def translateOperation(s: Statement, cenv: CEnvironment): (ProofStep, CEnvironment) = s match {
      case Skip =>
        (EmpStep(cenv), cenv)
      case Load(to, _, from, _) =>
        (ReadStep(CVar(to.name), CVar(from.name)), cenv)
      case Store(to, offset, e) =>
        val frame = item.node.goal.callGoal.isEmpty
        (WriteStep(CVar(to.name), offset, translateExpr(e), frame), cenv)
      case Malloc(to, tpe, sz) =>
        (AllocStep(CVar(to.name), translateSSLType(tpe), sz), cenv)
      case Free(v) =>
        val block = item.node.footprint.pre.sigma.blocks.find(_.loc == v)
        assert(block.nonEmpty)
        (FreeStep(block.get.sz), cenv)
    }

    def translateProducer(stmtProducer: StmtProducer, cenv: CEnvironment): (ProofProducer, CEnvironment) = {
      stmtProducer match {
        case ChainedProducer(p1, p2) =>
          val (k1, cenv1) = translateProducer(p1, cenv)
          val (k2, cenv2) = translateProducer(p2, cenv1)
          (k1 >> k2, cenv2)
        case PartiallyAppliedProducer(p, _) =>
          translateProducer(p, cenv)
        case FrameProducer(h) =>
          h match {
            case _: Block =>
              (IdProofProducer, cenv)
            case _ =>
              val framedHeaplets = cenv.framedHeaplets :+ translateHeaplet(h)
              (IdProofProducer, cenv.copy(framedHeaplets = framedHeaplets))
          }
        case EnterCall(goal) =>
          val cgoal = translateGoal(goal)
          (IdProofProducer, cenv.copy(subst = Map.empty, call = Some(cgoal, cenv.ghostSubst, cenv.subst)))
        case ExitCall =>
          assert(item.node.goal.callGoal.isDefined)
          val callGoal = item.node.goal.callGoal.get
          val (initialGoal, prevGhostSubst, prevSubst) = cenv.call.get

          // create call step
          val companionToFresh = callGoal.companionToFresh.map{ case (k, v) => CVar(k.name) -> CVar(v.name)}
          val freshToActual = callGoal.freshToActual.map{ case (k, v) => CVar(k.name) -> translateExpr(v)}
          val outsideVars = initialGoal.programVars ++ initialGoal.universalGhosts
          val pureEx = cenv.spec.pureParams.map(_._2).map(v => v.subst(companionToFresh)).map(v => v.subst(freshToActual))
          val pre = initialGoal.post.subst(freshToActual)
          val post = translateAsn(callGoal.calleePost).subst(freshToActual)

          // end of call; reset subst map
          val cenv1 = cenv.copy(ghostSubst = prevGhostSubst, subst = prevSubst, call = None)

          (PrependProofProducer(CallStep(pre, post, outsideVars, pureEx)), cenv1)
        case SubstProducer(subst) =>
          val csub = subst.map { case (v, e) => CVar(v.name) -> translateExpr(e) }
          val cenv1 = cenv.copy(subst = cenv.subst ++ csub)
          (IdProofProducer, cenv1)
        case GhostSubstProducer(subst) =>
          val csub = subst.map { case (v, e) => CVar(v.name) -> CVar(e.name) }
          val cenv1 = cenv.copy(ghostSubst = cenv.ghostSubst ++ csub)
          (IdProofProducer, cenv1)
        case UnrollProducer(app, selector, expansion, substEx) =>
          val cselector = translateExpr(selector)
          val capp = translateHeaplet(app).asInstanceOf[CSApp]
          val csub = substEx.map { case (src, dst) => CVar(src.name) -> CVar(dst.name) }
          val cexpansion = translateSFormula(expansion)

          // get clause existentials
          val predicate = cenv.predicates.find(_.name == app.pred).get
          val clauseIdx = predicate.clauses.indexWhere(_.selector == cselector)
          val varsInExpansion = cexpansion.vars.distinct
          val clauseExUnordered = csub.values.toList
          val clauseEx = varsInExpansion.filter(clauseExUnordered.contains)

          val item = AppExpansion(clauseIdx, cexpansion, clauseEx)
          val heapSubst = cenv.heapSubst ++ Map(capp -> item)
          val cenv1 = cenv.copy(heapSubst = heapSubst)
          (IdProofProducer, cenv1)
        case ConstProducer(s) =>
          val (step, cenv1) = translateOperation(s, cenv)
          (ConstProofProducer(step), cenv1)
        case PrependProducer(s) =>
          if (s.isInstanceOf[Call]) return (IdProofProducer, cenv)
          val (step, cenv1) = translateOperation(s, cenv)
          (PrependProofProducer(step), cenv1)
        case BranchProducer(_) =>
          val sapp = translateHeaplet(item.node.footprint.pre.sigma.apps.head).asInstanceOf[CSApp]
          val subgoals = item.node.children.map(n => translateGoal(n.goal))
          (BranchProofProducer(sapp, subgoals), cenv)
        case GuardedProducer(_, _) =>
          (GuardedProofProducer, cenv)
        case _ =>
          (IdProofProducer, cenv)
      }
    }

    def generateNextItems(p: ProofProducer, cenv: CEnvironment): Seq[TraversalItem] = {
      item.node.children.map(node => TraversalItem(node, cenv))
    }

    // handle guard
    def updateProducerPost(nextItems: Seq[TraversalItem], nextKont: ProofProducer, cenv: CEnvironment): ProofProducer = nextKont match {
      case _: Branching =>
        nextItems.tail.foldLeft(nextKont >> kont) {
          case (foldedP, item) => FoldProofProducer(traverseProof, item, foldedP)
        }
      case _ =>
        nextKont >> kont
    }

    // generate nested continuations + environments for children
    val (p0, cenv1) = translateProducer(item.node.kont, item.cenv)
    val p = p0.simplify
    val nextItems = generateNextItems(p, cenv1)
    val nextKont = updateProducerPost(nextItems, p, cenv1)

      nextItems.headOption match {
      case Some(childHead) =>
        traverseProof(childHead, nextKont)
      case None =>
        nextKont(Nil)
    }
  }
}
