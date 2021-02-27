package org.tygus.suslik.certification

import org.tygus.suslik.certification.targets.htt.HTT
import org.tygus.suslik.certification.targets.iris.Iris
import org.tygus.suslik.certification.targets.vst.VST
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

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
  def certify(proc: Procedure, env: Environment): Certificate[T,P]
  def mkDefs(predicates: List[P]): String
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

    override def certify(proc: Procedure, env: Environment): Certificate[T,P] = ???

    override def mkDefs(predicates: List[P]): String = ???
  }
}
