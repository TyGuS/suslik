package org.tygus.synsl.synthesis

import org.tygus.synsl.language.Statements
import org.tygus.synsl.logic.{Assertion, Environment, Spec}

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Rules {

  import Statements._

  type Pre = Assertion
  type Post = Assertion

  // A continuation for synthesizing the "larger" statement from substatement
  type StmtProducer = Seq[Statement] => Statement

  abstract sealed class RuleResult

  /**
    * Rule is not applicable
    */
  case class Fail() extends RuleResult

  /**
    * Rule is applicable and produces:
    * - a sequence of subgoals (premises fo the rule)
    * - a producer: continuation that combines the results of the subgoals into the final statement
    * An empty list of subgoals paired with an constant producer denotes a leaf in the synthesis derivation
    */
  case class MoreGoals(goals: Seq[Spec], kont: StmtProducer) extends RuleResult

  /**
    * A generic class for a deductive rule to be applied
    */
  abstract class Rule extends RuleUtils {
    // Apply the rule and get the subgoals
    def apply(spec: Spec, env: Environment): RuleResult

  }

}
