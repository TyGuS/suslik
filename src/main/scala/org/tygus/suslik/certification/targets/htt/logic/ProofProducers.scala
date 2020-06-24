package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.{CInductiveClause, CInductivePredicate}
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.Proof.CGoal
import org.tygus.suslik.certification.targets.htt.logic.ProofSteps.{AbduceBranchStep, OpenPostStep, OpenStep, ProofStep, SeqCompStep}

object ProofProducers {
  type Kont = Seq[ProofStep] => ProofStep

  trait Branching

  sealed abstract class ProofProducer {
    val arity: Int
    val fn: Kont

    def apply(children: Seq[ProofStep]): ProofStep = {
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
      case ChainedProofProducer(_, p2@ConstProofProducer(_)) => p2.simplify
      case _ => this
    }
  }

  case class ChainedProofProducer(p1: ProofProducer, p2: ProofProducer) extends ProofProducer {
    val arity: Int = p1.arity + p2.arity - 1
    val fn: Kont = steps => {
      val (steps1, steps2) = steps.splitAt(p1.arity)
      val step = p1.fn(steps1)
      p2.fn(step +: steps2)
    }
  }

  case class PartiallyAppliedProofProducer(p: ProofProducer, s: ProofStep) extends ProofProducer {
    val arity: Int = p.arity - 1
    val fn: Kont = steps => {
      p.apply(s +: steps)
    }
  }

  case object IdProofProducer extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = _.head
  }

  case class ConstProofProducer(step: ProofStep) extends ProofProducer {
    val arity: Int = 0
    val fn: Kont = _ => step
  }

  case class PrependProofProducer(s: ProofStep) extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = steps => SeqCompStep(s, steps.head).simplify
  }

  case class AppendProofProducer(s: ProofStep) extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = steps => SeqCompStep(steps.head, s).simplify
  }

  case class BranchProofProducer(app: CSApp, subgoals: Seq[CGoal]) extends ProofProducer with Branching {
    val arity: Int = subgoals.length
    val fn: Kont = steps =>
      if (steps.length == 1) steps.head else {
        val condBranches = steps.zip(subgoals).reverse.map{ case (s, g) =>
          SeqCompStep(OpenPostStep(app, g), s)
        }
        val ctail = condBranches.tail
        val finalBranch = condBranches.head
        SeqCompStep(OpenStep, ctail.foldLeft(finalBranch) { case (eb, tb) => SeqCompStep(tb, eb) })
      }
  }

  case object GuardedProofProducer extends ProofProducer with Branching {
    val arity: Int = 2
    val fn: Kont = steps =>
      if (steps.length == 1) steps.head else {
        val condBranches = steps.reverse
        val ctail = condBranches.tail
        val finalBranch = condBranches.head
        SeqCompStep(AbduceBranchStep, ctail.foldLeft(finalBranch) { case (eb, tb) => SeqCompStep(tb, eb) })
      }
  }

  case class FoldProofProducer[T](op: (T, ProofProducer) => ProofStep, item: T, bp: ProofProducer) extends ProofProducer {
    val arity: Int = 1
    val fn: Kont = steps => {
      // partially apply a produced step to the BranchProducer of the downstream `bp`
      @scala.annotation.tailrec
      def isBase(curr: ProofProducer): Boolean = curr match {
        case PartiallyAppliedProofProducer(p, _) => isBase(p)
        case _: Branching => true
        case _ => false
      }
      def update(curr: ProofProducer): ProofProducer = curr match {
        case FoldProofProducer(op, item, bp) => FoldProofProducer(op, item, update(bp))
        case ChainedProofProducer(p1, p2) => ChainedProofProducer(update(p1), update(p2))
        case _: PartiallyAppliedProofProducer | _: Branching if isBase(curr) => curr.partApply(steps.head)
        case _ => curr
      }
      op(item, update(bp))
    }
  }
}