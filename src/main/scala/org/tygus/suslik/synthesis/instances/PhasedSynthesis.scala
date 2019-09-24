package org.tygus.suslik.synthesis.instances

import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.smt.SMTSolving.sat
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.util.SynLogging

class PhasedSynthesis(implicit val log: SynLogging) extends Synthesis {

  {
    // Warm-up the SMT solver on start-up to avoid future delays
    for (i <- 1 to 5; j <- 1 to 2; k <- 1 to 3) {
      sat(BinaryExpr(OpLeq, IntConst(i), BinaryExpr(OpPlus, IntConst(j), IntConst(k))))
    }
  }

  def allRules(goal: Goal): List[SynthesisRule] = {
    val config = goal.env.config
    anyPhaseRules(config) ++ unfoldingPhaseRules(config) ++ flatPhaseRules(config)
  }

  def nextRules(goal: Goal, depth: Int): List[SynthesisRule] = {
    val config = goal.env.config
    if (!config.phased)
    // Phase distinction is disabled: use all non top-level rules
      allRules(goal)
    else if (goal.hasPredicates)
    // Unfolding phase
      anyPhaseRules(config) ++ unfoldingPhaseRules(config)
    else
    // Flat phase
      anyPhaseRules(config) ++ flatPhaseRules(config)
  }


  def anyPhaseRules(config: SynConfig):  List[SynthesisRule] = List(
    // Normalization rules
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    if (!config.fail) FailRules.Noop else FailRules.PostInconsistent,
//    LogicalRules.SubstLeftVar,

    OperationalRules.ReadRule,
//    OperationalRules.AllocRule,
  )

  def unfoldingPhaseRules(config: SynConfig):  List[SynthesisRule] = {
    val flags = config.flags
    if (flags(1) && flags(9))
    List(
      LogicalRules.SubstLeftVar,
      UnfoldingRules.Close,
      LogicalRules.FrameUnfolding,
      UnfoldingRules.CallRule,
      UnfoldingRules.Open,
      UnificationRules.HeapUnifyUnfolding,
      UnfoldingRules.AbduceCall,
    ) else if (flags(2) && flags(9))
      List(
        LogicalRules.SubstLeftVar,
        UnfoldingRules.AbduceCall,
        UnificationRules.HeapUnifyUnfolding,
        LogicalRules.FrameUnfolding,
        UnfoldingRules.CallRule,
        UnfoldingRules.Open,
        UnfoldingRules.Close,
      ) else if (flags(3) && flags(9))
      List(
        LogicalRules.SubstLeftVar,
        UnfoldingRules.CallRule,
        UnfoldingRules.Close,
        UnfoldingRules.AbduceCall,
        LogicalRules.FrameUnfolding,
        UnfoldingRules.Open,
        UnificationRules.HeapUnifyUnfolding,
      )else
      List(
        LogicalRules.SubstLeftVar,
        LogicalRules.FrameUnfolding,
        UnfoldingRules.CallRule,
        UnfoldingRules.Open,
        UnificationRules.HeapUnifyUnfolding,
        UnfoldingRules.AbduceCall,
        UnfoldingRules.Close,
      )
  }

  def flatPhaseRules(config: SynConfig): List[SynthesisRule] = {
    val flags = config.flags
    if (flags(0) && flags(9)) {
    List(

      OperationalRules.AllocRule,
      OperationalRules.WriteRuleOld,

      if (config.branchAbduction) FailRules.AbduceBranch else if (!config.fail) FailRules.Noop else FailRules.PostInvalid,
    LogicalRules.EmpRule,

    // Flat phase rules
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    UnificationRules.HeapUnifyFlat,

//    OperationalRules.WriteRule,
    OperationalRules.FreeRule,
    if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,

    UnificationRules.PureUnify,
    UnificationRules.Pick,
    UnificationRules.PickFromEnvRule,
  )
  }  else  if (flags(4) && flags(9)) {
      List(
        OperationalRules.WriteRuleOld,
        UnificationRules.HeapUnifyFlat,
        OperationalRules.AllocRule,

        if (config.branchAbduction) FailRules.AbduceBranch else if (!config.fail) FailRules.Noop else FailRules.PostInvalid,
        LogicalRules.EmpRule,

        // Flat phase rules
        LogicalRules.SubstLeft,
        UnificationRules.SubstRight,
        LogicalRules.FrameFlat,

        //    OperationalRules.WriteRule,
        OperationalRules.FreeRule,
        if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,

        UnificationRules.PureUnify,
        UnificationRules.Pick,
        UnificationRules.PickFromEnvRule,
      )
    } else  if (flags(5) && flags(9)) {
      List(
        UnificationRules.HeapUnifyFlat,
        OperationalRules.WriteRuleOld,
        OperationalRules.AllocRule,

        if (config.branchAbduction) FailRules.AbduceBranch else if (!config.fail) FailRules.Noop else FailRules.PostInvalid,
        LogicalRules.EmpRule,

        // Flat phase rules
        LogicalRules.SubstLeft,
        UnificationRules.SubstRight,
        LogicalRules.FrameFlat,

        //    OperationalRules.WriteRule,
        OperationalRules.FreeRule,
        if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,

        UnificationRules.PureUnify,
        UnificationRules.Pick,
        UnificationRules.PickFromEnvRule,
      )
    }  else //default
      List(
        if (config.branchAbduction) FailRules.AbduceBranch else if (!config.fail) FailRules.Noop else FailRules.PostInvalid,
        LogicalRules.EmpRule,

        // Flat phase rules
        LogicalRules.SubstLeft,
        UnificationRules.SubstRight,
        LogicalRules.FrameFlat,
        UnificationRules.HeapUnifyFlat,
        OperationalRules.AllocRule,
        OperationalRules.WriteRuleOld,

        //    OperationalRules.WriteRule,
        OperationalRules.FreeRule,
        if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,

        UnificationRules.PureUnify,
        UnificationRules.Pick,
        UnificationRules.PickFromEnvRule,
      )
  }

}
