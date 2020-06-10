package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification.Certificate

case class CoqCertificate(body: String, name: String) extends Certificate {
  val suffix: String = ".v"
}
