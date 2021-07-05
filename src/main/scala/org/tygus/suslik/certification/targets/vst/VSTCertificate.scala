package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.{Certificate, CertificateOutput, ClangOutput, ClangOutputWithCompilationUnit, CoqOutput}
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Proof
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate

case class VSTCertificate(testName: String, name:String, CProcedureDefinition: CProcedureDefinition, Proof: Proof) extends Certificate[VST, VSTPredicate] {
  override val predicates: List[VSTPredicate] = Proof.predicates

  override def outputs: List[CertificateOutput] = {
      List(
        ClangOutput(name + ".c", name, CProcedureDefinition.pp),
        CoqOutput("verif_" + name + ".v", "verif_" + name, Proof.pp)
      )
  }

  override def outputs_with_common_predicates(base_filename: String, common_predicates: List[VSTPredicate]): List[CertificateOutput] =
 {
  List(
  ClangOutputWithCompilationUnit(name + ".c", name, CProcedureDefinition.pp_with_common_defs(base_filename, common_predicates), List(s"$base_filename.c")),
  CoqOutput("verif_" + name + ".v", "verif_" + name, Proof.pp_with_common_defs(base_filename, common_predicates))
  )
}

}
