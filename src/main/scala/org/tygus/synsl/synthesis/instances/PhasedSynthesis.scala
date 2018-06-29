package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.language.Expressions.BoolConst
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.synthesis.{Synthesis, SynthesisRule}
import org.tygus.synsl.synthesis.rules.{NormalizationRules, OperationalRules, SubtractionRules, UnfoldingRules}
import org.tygus.synsl.util.SynLogging

class PhasedSynthesis (implicit val log: SynLogging) extends Synthesis {

  val startingDepth = 27

  {
    // Warm-up the SMT solver on start-up to avoid future delays
    assert(SMTSolving.valid(BoolConst(true)))
  }

  val topLevelRules: List[SynthesisRule] = List(
    // Top-level induction
    UnfoldingRules.MkInductionRule,
  )

  // Right now the rule is fixed statically
  // TODO: apply dynamic heuristics for rule application
  val everyDayRules: List[SynthesisRule] = List(
    // Terminal
    SubtractionRules.EmpRule,

    // Normalization rules
    NormalizationRules.StarPartial,
    NormalizationRules.NilNotLval,
    NormalizationRules.SubstLeft,
    NormalizationRules.Inconsistency,
//    NormalizationRules.SubstRight,

    OperationalRules.ReadRule,
    UnfoldingRules.InvokeInductionRule,

    SubtractionRules.FrameExact,
    OperationalRules.WriteRule,

    //    UnfoldingRules.AbductWritesAndCallRule,
    UnfoldingRules.CallRule,
    UnfoldingRules.AbductWritesRule,
    SubtractionRules.HeapUnify,

    UnfoldingRules.CloseRule,

    OperationalRules.AllocRule,
    OperationalRules.FreeRule,

    SubtractionRules.HypothesisUnify,
    NormalizationRules.SubstRight,
    SubtractionRules.Pick,
    OperationalRules.PickFromEnvRule,

  )

}
