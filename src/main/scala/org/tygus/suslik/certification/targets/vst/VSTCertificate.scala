package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.{ClangOutput, Certificate, CertificateOutput, CertificationTarget, CoqOutput, Predicate}
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Proof

case class VSTCertificate(name:String, CProcedureDefinition: CProcedureDefinition, Proof: Proof) extends Certificate {
  override val target: CertificationTarget = VST
  override val predicates: List[Predicate] = Proof.predicates

  override def outputs: List[CertificateOutput] =
    List(
      ClangOutput(name + ".c", name, CProcedureDefinition.pp),
      CoqOutput("verif_" + name + ".v", "verif_" + name, Proof.pp)
    )
}
