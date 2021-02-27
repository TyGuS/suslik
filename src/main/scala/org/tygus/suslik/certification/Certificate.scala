package org.tygus.suslik.certification

import java.io.File

import scala.sys.process.Process

abstract class CertificateOutput {
  val filename: String
  val name: String
  val body: String
  val isProof: Boolean = false
  def compile(dir: File): Int
}

case class ClangOutput(filename: String, name: String, body: String) extends CertificateOutput {
  def compile(dir: File): Int = {
    val cmd = Seq("clightgen", filename, "&&", "coqc", s"$name.v") // TODO: correct?
    Process(cmd, dir).!
  }
}

case class CoqOutput(filename: String, name: String, body: String) extends CertificateOutput {
  override val isProof: Boolean = true
  def compile(dir: File): Int = {
    val cmd = Seq("coqc", "-w", filename)
    Process(cmd, dir).!
  }
}

/**
  * A generic interface for certificates, to be implemented by all
  * certification backends
  */
trait Certificate {
  val predicates: List[Predicate]
  val target: CertificationTarget
  def outputs: List[CertificateOutput]
}
