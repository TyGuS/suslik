package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules.NormalizationRules._
import org.tygus.synsl.synthesis.rules.OperationalRules.{AllocRule, FreeRule, ReadRule, WriteRule}
import org.tygus.synsl.synthesis.rules.SubtractionRules.{EmpRule, Pick, StarIntro}
import org.tygus.synsl.synthesis.rules.UnfoldingRules.{CloseRule, OpenRule}
import org.tygus.synsl.synthesis.rules.{OperationalRules, SubtractionRules, _}

/**
  * @author Ilya Sergey
  */

class SimpleSynthesis extends Synthesis {

  val maxDepth = 25

  // Right now the rule is fixed statically
  // TODO: apply dynamic heuristics for rule application
  val rulesToApply: List[SynthesisRule] = List(

    // For experimentation
    SubtractionRules.Pick,

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


    //Unfolding rules
    UnfoldingRules.OpenRule,
    UnfoldingRules.CloseRule
    )

}
