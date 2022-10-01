package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.util.SynStats

abstract class SimpleSynthesis (config: SynConfig) extends Tactic {

  def nextRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (goal.isUnsolvable)
      Nil
    else if (goal.callGoal.nonEmpty) callAbductionRules(goal)
    else simpleRules(goal)
  }

  protected def callAbductionRules(goal: Goal): List[SynthesisRule] = {
    List(
      UnfoldingRules.CallRule,
      UnificationRules.SubstRight,
      FailRules.PostInconsistent,
      LogicalRules.FrameSimple,
      UnificationRules.HeapUnifySimple,
      UnificationRules.UnifyPointerSimple,
      OperationalRules.WriteSimple,
      UnificationRules.Pick)
  }

  protected def simpleRules(goal: Goal): List[SynthesisRule] = List(
    LogicalRules.NilNotLval,
    LogicalRules.EmpRule,
    LogicalRules.Inconsistency,
    FailRules.PostInconsistent,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    OperationalRules.ReadRule,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Open,
    UnfoldingRules.Close,
    LogicalRules.FrameSimple,
    UnificationRules.HeapUnifySimple,
    UnificationRules.UnifyPointerSimple,
    OperationalRules.FreeRule,
    OperationalRules.AllocRule,
    OperationalRules.WriteSimple,
    UnificationRules.Pick
 )

}

class AutomaticSimple(config: SynConfig) extends SimpleSynthesis(config) with AutomaticSynthesis
class InteractiveSimple(config: SynConfig, override val stats: SynStats) extends SimpleSynthesis(config) with InteractiveSynthesis
