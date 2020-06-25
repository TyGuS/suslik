package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.htt.language.CInductiveClause
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.Proof._
import org.tygus.suslik.certification.targets.htt.logic.ProofProducers._
import org.tygus.suslik.certification.targets.htt.logic.ProofSteps._
import org.tygus.suslik.certification.targets.htt.translation.Translation._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.UnfoldingRules.Close

object ProofTranslation {
  private case class TraversalItem(node: CertTree.Node, cenv: CEnvironment) extends Traversable

  def translate(node: CertTree.Node, proc: Procedure, goal: CGoal, cenv: CEnvironment): Proof = {
    val traversalItem = TraversalItem(node, cenv)
    val proofBody = traverseProof(traversalItem, PrependProofProducer(GhostElimStep(goal)))
    Proof(proofBody)
  }

  def traverseProof(item: TraversalItem, kont: ProofProducer): ProofStep = {
    def translateOperation(s: Statement, cenv: CEnvironment): (ProofStep, CEnvironment) = s match {
      case Skip =>
        (EmpStep(cenv.predicates, cenv.spec, cenv.subst, cenv.heapSubst), cenv)
      case Load(to, _, _, _) =>
        (ReadStep(CVar(to.name)), cenv)
      case Store(to, offset, e) =>
        (WriteStep(CVar(to.name), offset, translateExpr(e)), cenv)
      case Malloc(to, tpe, sz) =>
        (AllocStep(CVar(to.name), translateSSLType(tpe), sz), cenv)
      case Free(v) =>
        val block = item.node.consume.pre.blocks.find(_.loc == v)
        assert(block.nonEmpty)
        (FreeStep(block.get.sz), cenv)
      case Call(_, _, _) =>
        val csub = cenv.subst
        val sapp = translateHeaplet(item.node.consume.pre.apps.head).asInstanceOf[CSApp]
        val pureEx = cenv.spec.pureParams.filterNot(_._2.vars.exists(_.isCard)).map { case (_, v) => csub(v).asInstanceOf[CVar] }
        (CallStep(sapp, pureEx), cenv)
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
          val csub = subst.map { case (v, e) => CVar(v.name) -> translateExpr(e) }.filterKeys(!_.isCard)
          val cenv1 = cenv.copy(subst = cenv.subst ++ csub)
          (IdProofProducer, cenv1)
        case UnrollProducer(predName, clause, substEx) =>
          val csub = substEx.map { case (v, e) => CVar(v.name) -> translateExpr(e) }.filterKeys(!_.isCard)
          val src = translateHeaplet(item.node.consume.post.apps.head).asInstanceOf[CSApp]
          val dst = translateSFormula(item.node.children.head.produce.post)

          val pred = cenv.predicates.find(_.name == predName).get
          val selector = translateExpr(clause.selector)
          val clauseIdx = pred.clauses.indexWhere(_.selector == selector)
          val cclause = CInductiveClause(predName, clauseIdx, selector, translateAsn(clause.asn))
          val cenv1 = cenv.copy(subst = cenv.subst ++ csub, heapSubst = cenv.heapSubst ++ Map(src -> (dst, cclause)))
          (IdProofProducer, cenv1)
        case ConstProducer(s) =>
          val (step, cenv1) = translateOperation(s, cenv)
          (ConstProofProducer(step), cenv1)
        case PrependProducer(s) =>
          val (step, cenv1) = translateOperation(s, cenv)
          (PrependProofProducer(step), cenv1)
        case BranchProducer(_) =>
          val sapp = translateHeaplet(item.node.consume.pre.apps.head).asInstanceOf[CSApp]
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
