package org.tygus.synsl.synthesis

import org.tygus.synsl.logic.{Environment, PureLogicUtils, Spec}

/**
  * A generic class for a deductive rule to be applied
  *
  * @author Ilya Sergey
  */
abstract class SynthesisRule extends PureLogicUtils {
  // Apply the rule and get the subgoals
  def apply(spec: Spec, env: Environment): SynthesisRuleResult

}

abstract sealed class SynthesisRuleResult

/**
  * Rule is not applicable
  */
case object SynFail extends SynthesisRuleResult

/**
  * Rule is applicable and produces:
  * - a sequence of subgoals (premises fo the rule)
  * - a producer: continuation that combines the results of the subgoals into the final statement
  * An empty list of subgoals paired with an constant producer denotes a leaf in the synthesis derivation
  */
case class SynMoreGoals(goals: Seq[Spec], kont: StmtProducer) extends SynthesisRuleResult



