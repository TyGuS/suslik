package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.Certificate

case class HTTCertificate(body: String, name: String) extends Certificate {
  val suffix: String = ".v"
}
