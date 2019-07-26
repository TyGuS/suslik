package org.tygus.suslik.synthesis.instances

import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.smt.SMTSolving.sat
import org.tygus.suslik.synthesis._
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
    topLevelRules ++ anyPhaseRules(config) ++ unfoldingPhaseRules(config) ++ flatPhaseRules(config)
  }

  def nextRules(goal: Goal, depth: Int): List[SynthesisRule] = {
    val config = goal.env.config
    val rules = {
      if (goal.sketch != Hole)
      // Until we encounter a hole, symbolically execute the sketch
        symbolicExecutionRules(config)
      else if (!config.phased)
      // Phase distinction is disabled: use all non top-level rules
        anyPhaseRules(config) ++ unfoldingPhaseRules(config) ++ flatPhaseRules(config)
      else if (goal.hasPredicates)
      // Unfolding phase
        anyPhaseRules(config) ++ unfoldingPhaseRules(config)
      else
      // Flat phase
        anyPhaseRules(config) ++ flatPhaseRules(config)
    }
    if (depth == config.startingDepth) topLevelRules ++ rules
    else rules
  }


  def topLevelRules: List[SynthesisRule] = List(
    UnfoldingRules.InductionRule,
  )

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

  def symbolicExecutionRules(config: SynConfig):  List[SynthesisRule] = List(
    SymbolicExecutionRules.Open,
    SymbolicExecutionRules.GuidedRead,
    SymbolicExecutionRules.GuidedWrite,
    SymbolicExecutionRules.GuidedAlloc,
    SymbolicExecutionRules.GuidedFree,
    SymbolicExecutionRules.Conditional,
    SymbolicExecutionRules.GuidedCallRule,
    LogicalRules.EmpRule,
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    if (!config.fail) FailRules.Noop else FailRules.PostInconsistent,
    LogicalRules.SubstLeftVar,
    LogicalRules.FrameUnfolding,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.Close,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    UnificationRules.HeapUnifyFlat,
    if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,
    UnificationRules.PureUnify,
    UnificationRules.Pick,
    UnificationRules.PickFromEnvRule
  )

  def unfoldingPhaseRules(config: SynConfig):  List[SynthesisRule] = List(
    LogicalRules.SubstLeftVar,
    LogicalRules.FrameUnfolding,
    UnfoldingRules.CallRule,
    UnfoldingRules.Open,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Close,
  )

  def flatPhaseRules(config: SynConfig): List[SynthesisRule] = List(
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
