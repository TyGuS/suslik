package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.language.Expressions.BoolConst
import org.tygus.synsl.logic.Specifications.Goal
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.synthesis.{Synthesis, SynthesisRule}
import org.tygus.synsl.synthesis.rules._
import org.tygus.synsl.util.SynLogging

class PhasedSynthesis (implicit val log: SynLogging) extends Synthesis {

  val startingDepth = 100

  {
    // Warm-up the SMT solver on start-up to avoid future delays
    assert(SMTSolving.valid(BoolConst(true)))
  }

  def allRules: List[SynthesisRule] = topLevelRules ++ anyPhaseRules ++ unfoldingPhaseRules ++ flatPhaseRules
  def nextRules(goal: Goal, depth: Int): List[SynthesisRule] =
    if (depth == startingDepth)
      allRules
    else if (goal.hasPredicates)
      anyPhaseRules ++ unfoldingPhaseRules
    else
      anyPhaseRules ++ flatPhaseRules


  val topLevelRules: List[SynthesisRule] = List(
    UnfoldingRules.InductionRule,
  )

  val anyPhaseRules: List[SynthesisRule] = List(
    // Normalization rules
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    FailRules.PostInconsistent,
    OperationalRules.ReadRule,
//    OperationalRules.AllocRule,
  )

  val unfoldingPhaseRules: List[SynthesisRule] = List(
    LogicalRules.FrameUnfolding,
    UnfoldingRules.CallRule,
    UnfoldingRules.Open,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Close,
  )

  val flatPhaseRules: List[SynthesisRule] = List(
    LogicalRules.EmpRule,

    // Flat phase rules
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    FailRules.PostInvalid,
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
