package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget}

case class HTTCertificate(body: String, name: String) extends Certificate {
  val target: CertificationTarget = HTT

  def sanitize(txt: String): String = txt.replace('-', '_')
  // Replace hyphens with underscores
  override def outputs: List[CertificateOutput] =  List(CertificateOutput(None, sanitize(name), body))

}
