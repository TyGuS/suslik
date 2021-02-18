package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget}
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Proof

case class VSTCertificate(name:String, CProcedureDefinition: CProcedureDefinition, Proof: Proof) extends Certificate {
  override val target: CertificationTarget = VST

  override def outputs: List[CertificateOutput] =
    List(
      CertificateOutput(Some(name + ".c"), name, CProcedureDefinition.pp),
      CertificateOutput(None, "verif_" + name, Proof.pp)
    )
}
