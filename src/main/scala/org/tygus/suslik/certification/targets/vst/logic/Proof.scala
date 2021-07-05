package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.CoqOutput
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.ProofTreePrinter
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms._
import org.tygus.suslik.language.PrettyPrinting

object Proof {
  def helper_name (base_name: String) = s"${base_name}_predicates"

  /** prelude for Coq file */
  private def coq_prelude(import_names: List[String]) = s"""
Require Import VST.floyd.proofauto.
${import_names.map(lib_name => s"Require Import $lib_name.").mkString("\n")}
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

  def common_predicates(base_filename: String, predicates: List[VSTPredicate]) : CoqOutput = {
    val body : String =
      s"${Proof.coq_prelude(List(base_filename))}\n\n"+
        s"${predicates.map(_.pp).mkString("\n") + "\n"}\n\n" +
        s"${predicates.flatMap(_.get_helpers).map(_.pp).mkString("\n")}"


    CoqOutput(s"${helper_name(base_filename)}.v", helper_name(base_filename),  body)
  }

}
case class Proof(
                  name: String, predicates: List[VSTPredicate],
                  spec: ProofTerms.FormalSpecification, steps: ProofTree[VSTProofStep],
                  helper_specs: Map[String, ProofTerms.FormalSpecification],
                  uses_free: Boolean = false, uses_malloc: Boolean = false
                ) extends PrettyPrinting {


  /** prelude for the lemma */
  private def lemma_prelude : String =
    s"""Lemma body_$name : semax_body Vprog Gprog f_$name ${name}_spec.
       |Proof.
       |""".stripMargin

  private def library_spec : String = s"""Definition Gprog : funspecs :=
                                         |  ltac:(with_library prog [${name}_spec${
    if (uses_free) {"; free_spec"} else {""}
  }${
    if (uses_malloc) {"; malloc_spec"} else {""}
  }${
    if(helper_specs.nonEmpty) {";" ++ helper_specs.map(v => v._2.spec_name).mkString("; ")} else {""}
  }]).
                                         |""".stripMargin

  override def pp: String = {
    Proof.coq_prelude(List(name)) +
      (if (uses_free) { Proof.free_defs + "\n"  } else { "" }) +
      (if (uses_malloc) { Proof.malloc_defs + "\n"  } else { "" }) +
      predicates.map(_.pp).mkString("\n") + "\n" +
      helper_specs.values.map(_.pp).mkString("\n") + "\n" +
      spec.pp + "\n" +
      predicates.flatMap(_.get_helpers).map(_.pp).mkString("\n")  +"\n"+
      library_spec + "\n" +
      lemma_prelude +
      "start_function.\n" +
      "ssl_open_context.\n" +
      ProofTreePrinter.pp(steps) + "\n" +
    "Qed."
  }
  def pp_with_common_defs(base_filename: String, common_predicates: List[VSTPredicate]): String = {
    val defined_predicate_names = common_predicates.map(_.name).toSet
    val remaining_predicates = predicates.filterNot(v => defined_predicate_names.contains(v.name))
    s"${Proof.coq_prelude(List(Proof.helper_name(base_filename), name))}\n\n" +
       s"${if (uses_free) { Proof.free_defs + "\n"  } else { "" }}\n\n" +
       s"${if (uses_malloc) { Proof.malloc_defs + "\n"  } else { "" }}\n\n" +
       s"${remaining_predicates.map(_.pp).mkString("\n") + "\n"}\n\n" +
       s"${helper_specs.values.map(_.pp).mkString("\n") + "\n"}\n\n" +
       s"${spec.pp + "\n"}\n\n" +
       s"${remaining_predicates.flatMap(_.get_helpers).map(_.pp).mkString("\n")  +"\n"}\n\n" +
       s"${library_spec + "\n"}\n" +
       s"${lemma_prelude}\n" +
       "start_function.\n" +
       "ssl_open_context.\n" +
       s"${ProofTreePrinter.pp(steps) + "\n"}\n" +
       "Qed."
  }


}


