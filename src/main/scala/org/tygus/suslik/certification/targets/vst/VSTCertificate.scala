package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.{Certificate, CertificateOutput, ClangOutput, CoqOutput}
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Proof
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate

case class VSTCertificate(name:String, CProcedureDefinition: CProcedureDefinition, Proof: Proof) extends Certificate[VST, VSTPredicate] {
  override val predicates: List[VSTPredicate] = Proof.predicates

  override def outputs: List[CertificateOutput] =
    List(
      ClangOutput(name + ".c", name, CProcedureDefinition.pp),
      CoqOutput("verif_" + name + ".v", "verif_" + name, Proof.pp)
    )
}
