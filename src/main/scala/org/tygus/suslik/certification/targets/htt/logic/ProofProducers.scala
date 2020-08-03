package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.logic.Proof.CEnvironment
import org.tygus.suslik.certification.targets.htt.logic.ProofSteps._

object ProofProducers {
  type KontResult = (ProofStep, CEnvironment)
  type Kont = Seq[KontResult] => KontResult

  trait Branching

  sealed abstract class ProofProducer {
    val arity: Int
    val fn: Kont

    def apply(children: Seq[KontResult]): KontResult = {
      assert(children.lengthCompare(arity) == 0, s"Producer expects $arity children and got ${children.length}")
      fn(children)
    }

    def >>(p: ProofProducer): ProofProducer = {
      ChainedProofProducer(this, p)
    }

    def partApply(s: ProofStep): ProofProducer = {
      PartiallyAppliedProofProducer(this, s)
    }

    def simplify: ProofProducer = this match {
      case ChainedProofProducer(p1, IdProofProducer) => p1.simplify
      case ChainedProofProducer(IdProofProducer, p2) => p2.simplify
      case ChainedProofProducer(_, p2@ConstProofProducer(_, _)) => p2.simplify
      case _ => this
    }
  }

  case class ChainedProofProducer(p1: ProofProducer, p2: ProofProducer) extends ProofProducer {
    val arity: Int = p1.arity + p2.arity - 1
    val fn: Kont = res => {
      val (res1, res2) = res.splitAt(p1.arity)
      val r = p1.fn(res1)
      p2.fn(r +: res2)
    }
  }

  case class PartiallyAppliedProofProducer(p: ProofProducer, s: ProofStep) extends ProofProducer {
    val arity: Int = p.arity - 1
    val fn: Kont = res => {
      p.apply((s, res.head._2) +: res)
    }
  }

  case object IdProofProducer extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = _.head
  }

  case class ConstProofProducer(step: ProofStep, env: CEnvironment) extends ProofProducer {
    val arity: Int = 0
    val fn: Kont = _ => (step, env)
  }

  case class PrependProofProducer(s: ProofStep) extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = res => {
      val (step, env) = res.head
      (SeqCompStep(s.refreshGhostVars(env.ghostSubst), step).simplify, env)
    }
  }

  case class AppendProofProducer(s: ProofStep) extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = res => {
      val (step, env) = res.head
      (SeqCompStep(step, s.refreshGhostVars(env.ghostSubst)).simplify, env)
    }
  }

  /**
    *
    * @param openPostSteps the steps to perform upon entering each branch
    * @param branchEnv the state of the environment at the time of branching
    */
  case class BranchProofProducer(openPostSteps: Seq[OpenPostStep], branchEnv: CEnvironment) extends ProofProducer with Branching {
    val arity: Int = openPostSteps.length
    val fn: Kont = res =>
      if (res.length == 1) res.head else {
        // For each certified branch, prepend the step that prepares the branch's execution
        val condBranches = res.zip(openPostSteps).reverse.map { case ((s, env), openPost) =>
          SeqCompStep(openPost.refreshGhostVars(env.ghostSubst), s)
        }
        val ctail = condBranches.tail
        val finalBranch = condBranches.head

        // Compose the branch certification code in order, and prepend the Open step at the very beginning.
        // Discard envs propagated from child branches, and return the env that was preserved at the time of branching.
        (SeqCompStep(OpenStep, ctail.foldLeft(finalBranch) { case (eb, tb) => SeqCompStep(tb, eb) }), branchEnv)
      }
  }

  case class GuardedProofProducer(branchEnv: CEnvironment) extends ProofProducer with Branching {
    val arity: Int = 2
    val fn: Kont = res =>
      if (res.length == 1) res.head else {
        val condBranches = res.reverse.map(_._1)
        val ctail = condBranches.tail
        val finalBranch = condBranches.head
        (SeqCompStep(AbduceBranchStep, ctail.foldLeft(finalBranch) { case (eb, tb) => SeqCompStep(tb, eb) }), branchEnv)
      }
  }

  /**
    * One step in the CPS traversal of multiple branches. Partially applies the current branch's result to the
    * branch producer (`bp`), and then initiates the certification of the next branch. A BranchProofProducer of arity N
    * will have been fully applied after the N-th invocation of this FoldProofProducer.
    * @param op a procedure that generates a KontResult
    * @param item The start of the next branch to traverse
    * @param bp the branch producer or its partially applied form
    * @tparam T the unit of traversal in the algorithm
    */
  case class FoldProofProducer[T](op: (T, ProofProducer) => KontResult, item: T, bp: ProofProducer) extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = res => {
      val step = res.head._1

      // Partially apply a produced step to the BranchProducer of the downstream `bp`
      @scala.annotation.tailrec
      def isBase(curr: ProofProducer): Boolean = curr match {
        case PartiallyAppliedProofProducer(p, _) => isBase(p)
        case _: Branching => true
        case _ => false
      }

      // Find the BranchProducer in the `bp`, and then partially apply `step`
      def update(curr: ProofProducer): ProofProducer = curr match {
        case FoldProofProducer(op, item, bp) => FoldProofProducer(op, item, update(bp))
        case ChainedProofProducer(p1, p2) => ChainedProofProducer(update(p1), update(p2))
        case _: PartiallyAppliedProofProducer | _: Branching if isBase(curr) => curr.partApply(step)
        case _ => curr
      }

      // Update the `bp` with the new result and step into the next branch
      op(item, update(bp))
    }
  }
}