package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.logic.Specifications.Goal
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.logic.smt.SMTSolving.sat
import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules._
import org.tygus.synsl.util.SynLogging

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
    if (depth == config.startingDepth)
      allRules(goal)
    else if (!config.phasesEnabled)
    // Phase distinction is disabled: use all non top-level rules
      anyPhaseRules(config) ++ unfoldingPhaseRules(config) ++ flatPhaseRules(config)
    else if (goal.hasPredicates)
    // Unfolding phase
      anyPhaseRules(config) ++ unfoldingPhaseRules(config)
    else
    // Flat phase
      anyPhaseRules(config) ++ flatPhaseRules(config)
  }


  def topLevelRules: List[SynthesisRule] = List(
    UnfoldingRules.InductionRule,
  )

  def anyPhaseRules(config: SynConfig):  List[SynthesisRule] = List(
    // Normalization rules
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    if (!config.failRulesEnabled) FailRules.Noop else FailRules.PostInconsistent,
//    LogicalRules.SubstLeftVar,
    OperationalRules.ReadRule,
//    OperationalRules.AllocRule,
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
    if (!config.failRulesEnabled) FailRules.Noop else if (config.branchAbductionEnabled) FailRules.AbduceBranch else FailRules.PostInvalid,
    LogicalRules.EmpRule,

    // Flat phase rules
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    UnificationRules.HeapUnifyFlat,
    OperationalRules.AllocRule,
    OperationalRules.WriteRule,
    OperationalRules.FreeRule,
    if (!config.failRulesEnabled) FailRules.Noop else FailRules.HeapUnreachable,

    UnificationRules.PureUnify,
    UnificationRules.Pick,
    UnificationRules.PickFromEnvRule,
  )

}
