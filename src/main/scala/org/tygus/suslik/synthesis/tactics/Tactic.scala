package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, SynthesisRule}
import org.tygus.suslik.util.SynStats

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

trait AutomaticSynthesis {
  def filterExpansions(allExpansions: Seq[RuleResult]): Seq[RuleResult] = allExpansions
}

trait InteractiveSynthesis {

  val stats: SynStats

  def filterExpansions(allExpansions: Seq[Rules.RuleResult]): Seq[Rules.RuleResult] = {
    // Interactive mode: ask user to pick an expansion
    val choice = if (allExpansions.length == 1) 0 else readInt
    if (0 < choice && choice <= allExpansions.size) {
      val res = allExpansions(choice - 1)
      stats.addExpansionChoice(choice)
      List(res)
    } else allExpansions
  }

}
