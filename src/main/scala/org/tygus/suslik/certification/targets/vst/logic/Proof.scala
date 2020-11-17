package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.language.Expressions.Expr
import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.{Debug, State}
import org.tygus.suslik.certification.targets.vst.logic.Proof
import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Var}
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements.{Skip, Store}
import org.tygus.suslik.logic.{PFormula, PointsTo, SFormula}
import org.tygus.suslik.synthesis.rules.{DelegatePureSynthesis, FailRules, LogicalRules, OperationalRules, UnificationRules}
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}


case class Proof(steps: List[ProofSteps]) extends PrettyPrinting {
  override def pp: String =
    "start_function.\n" +
      "ssl_open_context.\n" +
      steps.map(_.pp).mkString("\n")
}


