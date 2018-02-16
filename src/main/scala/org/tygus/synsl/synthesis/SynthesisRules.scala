package org.tygus.synsl.synthesis

import org.tygus.synsl.language.Statements
import org.tygus.synsl.logic.{Assertion, Environment, LogicUtils, Spec}

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait SynthesisRules {

  import Statements._

  type Pre = Assertion
  type Post = Assertion

  // A continuation for synthesizing the "larger" statement from substatement
  type StmtProducer = Seq[Statement] => Statement

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

  /**
    * A generic class for a deductive rule to be applied
    */
  abstract class SynthesisRule extends LogicUtils {
    // Apply the rule and get the subgoals
    def apply(spec: Spec, env: Environment): SynthesisRuleResult

  }

}
