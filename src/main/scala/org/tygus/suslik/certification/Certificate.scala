package org.tygus.suslik.certification

/**
  * A generic interface for certificates, to be implemented by all
  * certification backends
  */
trait Certificate {
  val body: String
  val name: String
  val target: CertificationTarget
  def fileName: String = name + target.suffix
}
