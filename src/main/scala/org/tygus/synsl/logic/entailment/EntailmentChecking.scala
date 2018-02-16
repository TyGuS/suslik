package org.tygus.synsl.logic.entailment

import org.tygus.synsl.logic.{Assertion, Environment, Spec}
import org.tygus.synsl.synthesis.RuleUtils


/**
  * @author Ilya Sergey
  */

trait EntailmentChecking extends RuleUtils {

  type Pre = Assertion
  type Post = Assertion

  /*
    TODO: Unify the definitions below with synthesis machinery,
    as discussed on Feb 13, 2018.
   */
  abstract sealed class EntRuleResult

  case object EntFail extends EntRuleResult

  case class EntMoreGoals(goals: Seq[Spec]) extends EntRuleResult

  abstract class EntailmentRule {
    def apply(spec: Spec, env: Environment): EntRuleResult
  }


}
