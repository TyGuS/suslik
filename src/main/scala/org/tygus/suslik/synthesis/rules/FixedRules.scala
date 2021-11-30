package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.logic.Specifications
import org.tygus.suslik.synthesis.rules.LogicalRules.EmpRule
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
sealed trait FixedRules extends SynthesisRule {
  def nextRule: List[FixedRules]
}

object FixedRules {

  def to_iterator (rules: List[FixedRules]) : Iterator[FixedRules] =
    rules.flatMap(rule => rule :: rule.nextRule).toIterator

  case object Emp extends SynthesisRule with FixedRules {

    override def nextRule: List[FixedRules] = List()

    override def apply(goal: Specifications.Goal): Seq[Rules.RuleResult] =
      EmpRule.apply(goal)
  }

}
