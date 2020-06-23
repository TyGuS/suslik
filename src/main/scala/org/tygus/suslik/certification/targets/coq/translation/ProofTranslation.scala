package org.tygus.suslik.certification.targets.coq.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.logic.Proof._
import org.tygus.suslik.certification.targets.coq.logic.ProofProducers._
import org.tygus.suslik.certification.targets.coq.logic.ProofSteps._
import org.tygus.suslik.certification.targets.coq.translation.Translation._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.synthesis._

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
        (EmpStep(cenv.spec), cenv)
      case Load(to, _, _, _) =>
        (ReadStep(CVar(to.name)), cenv)
      case Store(to, _, e) =>
        (WriteStep(CVar(to.name), translateExpr(e)), cenv)
      case Malloc(to, tpe, sz) =>
        (AllocStep(CVar(to.name), translateSSLType(tpe), sz), cenv)
      case Free(v) =>
        val block = item.node.consume.pre.blocks.find(_.loc == v)
        assert(block.nonEmpty)
        (FreeStep(block.get.sz), cenv)
      case Call(_, _, _) =>
        val csub = cenv.existentials
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
        case ExistentialProducer(subst) =>
          val csub = subst.map { case (v, e) => CVar(v.name) -> translateExpr(e) }.filterKeys(!_.isCard)
          val cenv1 = cenv.copy(existentials = cenv.existentials ++ csub)
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
          (PrependProofProducer(AbduceBranchStep), cenv)
        case _ =>
          (IdProofProducer, cenv)
      }
    }

    def generateNextItems(p: ProofProducer, cenv: CEnvironment): Seq[TraversalItem] = {
      item.node.children.map(node => TraversalItem(node, cenv))
    }

    // handle guard
    def updateProducerPost(nextItems: Seq[TraversalItem], nextKont: ProofProducer, cenv: CEnvironment): ProofProducer = nextKont match {
      case _: BranchProofProducer =>
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
