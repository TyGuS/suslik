package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.language.Expressions.Expr
import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.{Debug, State}
import org.tygus.suslik.certification.targets.vst.logic.Proof
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Var}
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements.{Skip, Store}
import org.tygus.suslik.logic.{PFormula, PointsTo, SFormula}
import org.tygus.suslik.synthesis.rules.{DelegatePureSynthesis, FailRules, LogicalRules, OperationalRules, UnificationRules}
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}


case class Proof(name: String, predicates: List[VSTPredicate], spec: ProofTerms.FormalSpecification, steps: ProofTree[VSTProofStep], uses_free: Boolean = false, uses_malloc: Boolean = false) extends PrettyPrinting {

  /** prelude for Coq file */
  private def coq_prelude = s"""
Require Import VST.floyd.proofauto.
Require Import $name.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

"""

  /** C standard library specs */
  private def free_defs : String = """Definition free_spec :=
                              |  DECLARE _free
                              |          WITH ty: type, x: val
                              |                              PRE  [ (tptr tvoid) ]
                              |                              PROP()
                              |                              PARAMS(x)
                              |                              SEP (data_at_ Tsh ty x)
                              |                              POST [ Tvoid ]
                              |                              PROP()
                              |                              LOCAL()
                              |                              SEP (emp).
                              |""".stripMargin

  private def malloc_defs : String = """Definition malloc_spec :=
                                       |  DECLARE _malloc
                                       |        WITH t: type
                                       |        PRE [ tuint ]
                                       |        PROP()
                                       |        PARAMS(Vint (Int.repr (sizeof t)))
                                       |        SEP()
                                       |        POST [tptr tvoid] EX p:_,
                                       |        PROP()
                                       |        RETURN(p)
                                       |        SEP(data_at_ Tsh t p).
                                       |""".stripMargin

  /** prelude for the lemma */
  private def lemma_prelude : String =
    s"""Lemma body_$name : semax_body Vprog Gprog f_$name ${name}_spec.
       |Proof.
       |""".stripMargin

  private def library_spec : String = s"""Definition Gprog : funspecs :=
                                         |  ltac:(with_library prog [${name}_spec${ if (uses_free) {"; free_spec"} else {""}}${
    if (uses_malloc) {"; malloc_spec"} else {""}
  }]).
                                         |""".stripMargin

  override def pp: String = {
    coq_prelude +
    (if (uses_free) { free_defs + "\n"  } else { "" }) +
     (if (uses_malloc) { malloc_defs + "\n"  } else { "" }) +
      predicates.map(_.pp).mkString("\n") + "\n" +
      spec.pp + "\n" +
      predicates.flatMap(_.get_helpers).map(_.pp).mkString("\n")  +"\n"+
      library_spec + "\n" +
    lemma_prelude +
    "start_function.\n" +
      "ssl_open_context.\n" +
      steps.pp + "\n" +
    "Qed."
  }
}


