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

case class ClangHeaderOutput(filename: String, name: String, body: String) extends CertificateOutput {
  def compile (dir: File) : Int = { 0 }
}

/**
  * represents a synthesized C program with an additional compilation unit
  * @param filename
  * @param name
  * @param body
  * @param other_files
  */
case class ClangOutputWithCompilationUnit(filename: String, name: String, body: String, other_files: List[String]) extends CertificateOutput {
  def compile(dir: File): Int = {
    def to_cmd (cmd: Seq[String]) = Process(cmd, dir)
    val build_cmd = to_cmd(Seq("clightgen", "-normalize") ++ other_files ++ Seq(filename))
    val verify_cmd = to_cmd(Seq("coqc", "-w", "none", s"${name}.v"))
    build_cmd.#&&(verify_cmd).!
  }
}


case class ClangOutput(filename: String, name: String, body: String) extends CertificateOutput {
  def compile(dir: File): Int = {
    def to_cmd (cmd: Seq[String]) = Process(cmd, dir)
    val build_cmd = to_cmd(Seq("clightgen", "-normalize", filename))
    val verify_cmd = to_cmd(Seq("coqc", "-w", "none", s"${name}.v"))
    build_cmd.#&&(verify_cmd).!
  }
}



case class CoqOutput(filename: String, name: String, body: String) extends CertificateOutput {
  override val isProof: Boolean = true
  def compile(dir: File): Int = {
    val cmd = Seq("coqc", "-w", "none", filename)
    Process(cmd, dir).!
  }
}

/**
  * A generic interface for certificates, to be implemented by all
  * certification backends
  */
trait Certificate[T <: CertificationTarget, P <: Predicate] {
  val testName: String
  val predicates: List[P]

  /** return a list of outputs */
  def outputs: List[CertificateOutput]

  /**
    * Return list of certification outputs, assuming that predicates in common_predicates have been exported to a common file
    */
  def outputs_with_common_predicates(base_filename: String, common_predicates: List[P]): List[CertificateOutput] = outputs
}
