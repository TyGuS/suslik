package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.language.Expressions.BoolConst
import org.tygus.synsl.logic.Specifications.Goal
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules._
import org.tygus.synsl.util.SynLogging

/**
  * @author Ilya Sergey
  */

class SimpleSynthesis(implicit val log: SynLogging) extends Synthesis {

  val startingDepth = 27

  {
    // Warm-up the SMT solver on start-up to avoid future delays
    assert(SMTSolving.valid(BoolConst(true)))
  }

  def allRules: List[SynthesisRule] = topLevelRules ++ everyDayRules
  def nextRules(goal: Goal, depth: Int): List[SynthesisRule] =
    if (depth < startingDepth) everyDayRules else allRules


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
