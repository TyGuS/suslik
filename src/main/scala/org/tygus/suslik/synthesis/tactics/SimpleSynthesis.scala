package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, SynthesisRule}

class SimpleSynthesis (config: SynConfig) extends Tactic {

  def filterExpansions(allExpansions: Seq[RuleResult]): Seq[RuleResult] = allExpansions

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
      FailRules.CheckPost,
      LogicalRules.FrameSimple,
      UnificationRules.HeapUnifySimple,
      UnificationRules.HeapUnifyPointer,
      UnificationRules.PickArg,
      UnificationRules.PickCard,
      OperationalRules.WriteRule,
      UnificationRules.Pick)
  }

  protected def simpleRules(goal: Goal): List[SynthesisRule] = List(
//    LogicalRules.StarPartial,
//    LogicalRules.NilNotLval,
    LogicalRules.EmpRule,
    LogicalRules.Inconsistency,
    FailRules.PostInconsistent,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    OperationalRules.ReadRule,
    LogicalRules.FrameSimple,
    UnificationRules.HeapUnifySimple,
    UnificationRules.HeapUnifyPointer,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Open,
    UnfoldingRules.Close,
    OperationalRules.FreeRule,
    OperationalRules.AllocRule,
    UnificationRules.PickCard,
    OperationalRules.WriteRule,
    UnificationRules.Pick
 )

}
