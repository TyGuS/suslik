package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.language.Expressions.BoolConst
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.synthesis.{Synthesis, SynthesisRule}
import org.tygus.synsl.synthesis.rules.{NormalizationRules, OperationalRules, SubtractionRules, UnfoldingRules}
import org.tygus.synsl.util.SynLogging

class PhasedSynthesis (implicit val log: SynLogging) extends Synthesis {

  val startingDepth = 40

  {
    // Warm-up the SMT solver on start-up to avoid future delays
    assert(SMTSolving.valid(BoolConst(true)))
  }

  val topLevelRules: List[SynthesisRule] = List(
    // Top-level induction
    UnfoldingRules.InductionRule,
  )

  val everyDayRules: List[SynthesisRule] = List(
    // Terminal
    SubtractionRules.EmpRule,

    // Normalization rules
    NormalizationRules.StarPartial,
    NormalizationRules.NilNotLval,
    NormalizationRules.Inconsistency,
    OperationalRules.ReadRule,

    // Predicate phase rules
    SubtractionRules.FramePred,
    UnfoldingRules.CallRule,
    UnfoldingRules.Open,
    SubtractionRules.HeapUnifyPred,
    UnfoldingRules.AbductWritesRule,
    UnfoldingRules.Close,


    // Flat phase rules
    NormalizationRules.SubstLeft,
    NormalizationRules.SubstRight,
    NormalizationRules.PureUnreachable,
    SubtractionRules.FrameFlat,
    SubtractionRules.HeapUnifyFlat,
    OperationalRules.AllocRule,
    OperationalRules.WriteRule,
    OperationalRules.FreeRule,
    NormalizationRules.HeapUnreachable,

    SubtractionRules.HypothesisUnify,
    SubtractionRules.Pick,
    OperationalRules.PickFromEnvRule,
  )

}
