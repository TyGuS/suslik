package org.tygus.suslik.certification

import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

trait CertificationTarget {
  val name: String
  def certify(proc: Procedure, env: Environment): Certificate
}
