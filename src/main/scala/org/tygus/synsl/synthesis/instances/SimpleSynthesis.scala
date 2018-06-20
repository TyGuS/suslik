package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules.{OperationalRules, SubtractionRules, _}
import org.tygus.synsl.util.SynLogging

/**
  * @author Ilya Sergey
  */

class SimpleSynthesis(implicit val log: SynLogging) extends Synthesis {

  val startingDepth = 27

  val topLevelRules: List[SynthesisRule] = List(
    // Top-level induction
    UnfoldingRules.InductionRule,
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
    NormalizationRules.SubstRight,
    // NormalizationRules.Hypothesis,

    // Subtraction rules
    SubtractionRules.StarIntro,
    SubtractionRules.HypothesisUnify,

    // Invertible operational rules
    OperationalRules.ReadRule,
    OperationalRules.WriteRule,

    // TODO: Only with this order of rules tree-morph succeeds!
    // If these come last, it goes to an eternal alloc/free spiral. :(
    // UnfoldingRules.ApplyHypothesisRule,

    UnfoldingRules.ApplyHypothesisAbduceFrameRule, // Experimental

    // Also, moving UnfoldingRules.ApplyHypothesisRule up makes things worse...
    UnfoldingRules.CloseRule,

    // Noninvertible operational rules
    // OperationalRules.WriteRuleOld,
    OperationalRules.AllocRule,
    OperationalRules.FreeRule,

    // For experimentation
    // SubtractionRules.Pick,

    OperationalRules.PickFromEnvRule,

  )

}
