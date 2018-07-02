package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.language.Expressions.BoolConst
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules._
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
    LogicalRules.EmpRule,

    // Normalization rules
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.SubstLeft,
    LogicalRules.Inconsistency,
    UnificationRules.SubstRight,

    OperationalRules.ReadRule,
    UnfoldingRules.Open,

    // Subtraction rules
    UnificationRules.StarIntro,

    // Invertible operational rules
    OperationalRules.WriteRule,

    // If these come last, it goes to an eternal alloc/free spiral. :(
    //    UnfoldingRules.AbductWritesAndCallRule,
    UnfoldingRules.CallRule,
    UnfoldingRules.AbduceCall,

    UnfoldingRules.Close,

    // Noninvertible operational rules
    // OperationalRules.WriteRuleOld,
    OperationalRules.AllocRule,
    OperationalRules.FreeRule,

    UnificationRules.PureUnify,
    UnificationRules.Pick,
    UnificationRules.PickFromEnvRule,

  )

}
