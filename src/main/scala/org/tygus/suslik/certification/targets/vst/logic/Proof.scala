package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.language.Expressions.Expr
import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.{Debug, State}
import org.tygus.suslik.certification.targets.vst.logic.Proof
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Var}
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements.{Skip, Store}
import org.tygus.suslik.logic.{PFormula, PointsTo, SFormula}
import org.tygus.suslik.synthesis.rules.{DelegatePureSynthesis, FailRules, LogicalRules, OperationalRules, UnificationRules}
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}


case class Proof(name: String, predicates: List[VSTPredicate], spec: ProofTerms.FormalSpecification, steps: ProofSteps) extends PrettyPrinting {

  /** prelude for Coq file */
  private def coq_prelude = s"""
Require Import VST.floyd.proofauto.
Require Import $name.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

"""

  private def lemma_prelude =
    s"""Lemma body_$name : semax_body Vprog Gprog f_$name ${name}_spec.
       |Proof.
       |""".stripMargin

  override def pp: String = {
    coq_prelude +
      predicates.map(_.pp).mkString("\n") +
      spec.pp + "\n" +
    lemma_prelude +
    "start_function.\n" +
      "ssl_open_context.\n" +
      steps.pp + "\n" +
    "Qed."
  }
}


