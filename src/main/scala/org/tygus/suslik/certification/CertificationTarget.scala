package org.tygus.suslik.certification

import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

/**
  * A generic interface for certification targets. The user can specify a target
  * by setting the command-line flag `certTarget` to the target's `name` property.
  */
trait CertificationTarget {
  val name: String
  val suffix: String
  def certify(proc: Procedure, env: Environment): Certificate
}
