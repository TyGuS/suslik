package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, SynthesisRule}

/**
  * a tactic guides search by pruning and prioritizing the children of an or-node
  */
trait Tactic {

  /**
    * Which rules should be considered when expanding node
    */
  def nextRules(node: OrNode): List[SynthesisRule]

  def filterExpansions(allExpansions: Seq[RuleResult]): Seq[RuleResult]

}
