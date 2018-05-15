package org.tygus.synsl.synthesis

import org.tygus.synsl.language.PrettyPrinting
import org.tygus.synsl.logic.{Environment, Goal, PureLogicUtils}

/**
  * A generic class for a deductive rule to be applied
  *
  * @author Ilya Sergey
  */
abstract class SynthesisRule extends PureLogicUtils {
  // Apply the rule and get all possible sub-derivations
  def apply(goal: Goal, env: Environment): Seq[Subderivation]
}

/**
  * A result of a rule application:
  * consists of sub-goals (rule premises) and
  * a statement producer that assembles the sub-goal results
  */
case class Subderivation(subgoals: Seq[(Goal, Environment)], kont: StmtProducer) extends PrettyPrinting {
  override def pp: String = s"${subgoals.size} subgoal(s):\n${subgoals.map { case (g, e) => s"${e.pp}${g.pp}" }.mkString("\n")}"
}



