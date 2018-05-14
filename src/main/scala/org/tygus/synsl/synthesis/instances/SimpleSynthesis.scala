package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules.{OperationalRules, SubtractionRules, _}
import org.tygus.synsl.util.SynLogging

/**
  * @author Ilya Sergey
  */

class SimpleSynthesis(implicit val log: SynLogging) extends Synthesis {

  val maxDepth = 25

  // Right now the rule is fixed statically
  // TODO: apply dynamic heuristics for rule application
  val rulesToApply: List[SynthesisRule] = List(
    // Top-level induction
    UnfoldingRules.InductionRule,

    // Terminal
    SubtractionRules.EmpRule,

    // Normalization rules
    NormalizationRules.StarPartial,
    NormalizationRules.NilNotLval,
    NormalizationRules.Hypothesis,
    NormalizationRules.StripEqPost,
    NormalizationRules.StripEqPre,
    NormalizationRules.SubstLeft,
    NormalizationRules.Inconsistency,
    NormalizationRules.SubstRight,

    // Subtraction rules
    SubtractionRules.StarIntro,

    // Operational rules
    OperationalRules.ReadRule,
    OperationalRules.WriteRule,
    OperationalRules.AllocRule,
    OperationalRules.FreeRule,

    // For experimentation
    SubtractionRules.Pick,

    //Unfolding rules
    UnfoldingRules.CloseRule,
  )

}
