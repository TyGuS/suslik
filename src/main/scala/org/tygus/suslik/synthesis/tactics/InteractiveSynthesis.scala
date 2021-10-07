package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.util.SynStats

class InteractiveSynthesis(config: SynConfig, stats: SynStats) extends PhasedSynthesis(config) {

  override def filterExpansions(allExpansions: Seq[(Rules.RuleResult, Double)]): Seq[(Rules.RuleResult, Double)] = {
    // Interactive mode: ask user to pick an expansion
    val choice = if (allExpansions.length == 1) 0 else readInt
    if (0 < choice && choice <= allExpansions.size) {
      val res = allExpansions(choice - 1)
      stats.addExpansionChoice(choice)
      List(res)
    } else allExpansions
  }

}
