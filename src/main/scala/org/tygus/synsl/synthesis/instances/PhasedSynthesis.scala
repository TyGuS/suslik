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

  def allRules: List[SynthesisRule] = topLevelRules ++ anyPhaseRules ++ unfoldingPhaseRules ++ flatPhaseRules
  def nextRules(goal: Goal, depth: Int): List[SynthesisRule] =
    if (depth == config.startingDepth)
      allRules
    else if (goal.hasPredicates)
      anyPhaseRules ++ unfoldingPhaseRules
    else
      anyPhaseRules ++ flatPhaseRules


  def topLevelRules: List[SynthesisRule] = List(
    UnfoldingRules.InductionRule,
  )

  def anyPhaseRules: List[SynthesisRule] = List(
    // Normalization rules
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    FailRules.PostInconsistent,
    OperationalRules.ReadRule,
//    OperationalRules.AllocRule,
  )

  def unfoldingPhaseRules: List[SynthesisRule] = List(
    LogicalRules.FrameUnfolding,
    UnfoldingRules.CallRule,
    UnfoldingRules.Open,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Close,
  )

  def flatPhaseRules: List[SynthesisRule] = List(
    if (config.branchAbductionEnabled) {
      FailRules.AbduceBranch
    } else {
      FailRules.PostInvalid
    },
    LogicalRules.EmpRule,

    // Flat phase rules
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    UnificationRules.HeapUnifyFlat,
    OperationalRules.AllocRule,
    OperationalRules.WriteRule,
    OperationalRules.FreeRule,
    FailRules.HeapUnreachable,

    UnificationRules.PureUnify,
    UnificationRules.Pick,
    UnificationRules.PickFromEnvRule,
  )

}
