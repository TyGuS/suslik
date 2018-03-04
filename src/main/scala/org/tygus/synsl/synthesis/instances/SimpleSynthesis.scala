package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules.{OperationalRules, SubtractionRules, _}

/**
  * @author Ilya Sergey
  */

class SimpleSynthesis extends Synthesis {

  val maxDepth = 25

  // Right now the rule is fixed statically
  // TODO: apply dynamic heuristics for rule application
  val rulesToApply: List[SynthesisRule] = List(

    // Normalization rules
    NormalizationRules.Hypothesis,
    NormalizationRules.StripEqPost,
    NormalizationRules.StripEqPre,
    NormalizationRules.SubstLeft,
    NormalizationRules.Inconsistency,

    // Subtraction rules
    SubtractionRules.EmpRule,
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
