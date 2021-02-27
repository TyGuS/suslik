package org.tygus.suslik.certification

case class CertificateOutput(filename: String, name: String, body: String, isProof: Boolean = true)
/**
  * A generic interface for certificates, to be implemented by all
  * certification backends
  */
trait Certificate {
  val predicates: List[Predicate]
  val target: CertificationTarget
  def outputs: List[CertificateOutput]
}
