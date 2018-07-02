package org.tygus.synsl.synthesis

import org.tygus.synsl.logic.Specifications._
import org.tygus.synsl.language.PrettyPrinting
import org.tygus.synsl.logic._

/**
  * A generic class for a deductive rule to be applied
  *
  * @author Ilya Sergey
  */
abstract class SynthesisRule extends PureLogicUtils {
  // Apply the rule and get all possible sub-derivations
  def apply(goal: Goal): Seq[Subderivation]

  // Is the rule enabled on this goal?
  def enabled(goal: Goal): Boolean

  def saveApplication(footprint: (Set[Int], Set[Int]),
                      currentDeriv: Derivation,
                      customCost: Option[Int] = None): RuleApplication = {
    val cost = customCost match {
      // By default, applications with earlier footprint have lower cost
      case None => footprint._1.union(footprint._2).min
      case Some(s) => s
    }
    RuleApplication(this, footprint, (currentDeriv.preIndex.length, currentDeriv.postIndex.length), cost)
  }
}

/**
  * Different kinds of rules
  */

// Invertible rule: does not restrict the set of derivations,
// so no need to backtrack in case of failure
trait InvertibleRule

trait AnyPhase {
  def enabled(goal: Goal): Boolean = true
}

trait UnfoldingPhase {
  def enabled(goal: Goal): Boolean = {
    goal.hasPredicates
  }

  def heapletFilter(h: Heaplet): Boolean = {
    h.isInstanceOf[SApp]
  }
}

trait FlatPhase {
  def enabled(goal: Goal): Boolean = {
    !goal.hasPredicates
  }

  def heapletFilter(h: Heaplet): Boolean = {
    true
  }
}

/**
  * A result of a rule application:
  * consists of sub-goals (rule premises) and
  * a statement producer that assembles the sub-goal results
  */
case class Subderivation(subgoals: Seq[Goal], kont: StmtProducer)
    extends PrettyPrinting with PureLogicUtils {

  override def pp: String =
    s"${subgoals.size} subgoal(s):\n${subgoals.map { g => s"${g.env.pp}${g.pp}" }.mkString("\n")}"
}




