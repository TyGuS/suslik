package org.tygus.suslik.certification

case class CertificateOutput(filename: Option[String], name: String, body: String)
/**
  * A generic interface for certificates, to be implemented by all
  * certification backends
  */
trait Certificate {
  /** returns the exported filename for a string */
  def getFileName(name: String) : String = name + target.suffix

  val target: CertificationTarget
  def outputs: List[CertificateOutput]
//  def fileName: String = name + target.suffix
}
