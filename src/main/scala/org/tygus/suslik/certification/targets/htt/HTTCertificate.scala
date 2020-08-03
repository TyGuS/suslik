package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.{Certificate, CertificationTarget}

case class HTTCertificate(body: String, name: String) extends Certificate {
  val target: CertificationTarget = HTT

  // Replace hyphens with underscores
  override def fileName: String = super.fileName.replace('-', '_')
}
