package org.tygus.suslik.certification

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.HTT
import org.tygus.suslik.certification.targets.iris.Iris
import org.tygus.suslik.certification.targets.vst.VST
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.logic.Specifications.Goal


/**
  * A generic interface for certification targets.
  * The user can specify a target by setting the command-line flag `certTarget` to the target's `name` property.
  */
trait CertificationTarget {
  /** uniquely identifies the certification target - users can specify
    * this certification target from the CLI passing `name` via the
    * `certTarget` flag */
  type T <: CertificationTarget
  type P <: Predicate
  val name: String
  val suffix: String
  def certify(testName: String, proc: Procedure, tree: ProofTree[SuslikProofStep], goal: Goal, env: Environment): Certificate[T,P]

  /**
    * Generate a list of outputs for the following predicates.
    * @param base_filename - base name of common file
    * @param predicates - list of predicates with common definitions
    * @return - a list of synthesized files for predicate definitions
    */
  def generate_common_definitions_of(base_filename: String, predicates: List[P]): List[CertificateOutput]
}

object CertificationTarget {
  def fromString(s: String): CertificationTarget = s match {
    case "htt" => HTT()
    case "vst" => VST()
    case "iris" => Iris()
    case _ => NoCert
  }

  object NoCert extends CertificationTarget {
    override type T = Nothing
    override type P = Nothing
    val name: String = ""
    override val suffix: String = ""

    override def certify(testName: String, proc: Procedure, tree: ProofTree[SuslikProofStep], goal: Goal, env: Environment): Certificate[T,P] = ???

    override def generate_common_definitions_of(base_filename: String, predicates: List[P]): List[CertificateOutput] = ???
  }
}
