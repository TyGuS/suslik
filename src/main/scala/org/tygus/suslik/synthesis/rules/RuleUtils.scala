package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.SSLException
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.synthesis.SymbolicExecutionError

/**
  * @author Ilya Sergey
  */

trait RuleUtils {

  val exceptionQualifier: String

  case class SynthesisRuleException(msg: String) extends SSLException(exceptionQualifier, msg)

  def ruleAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisRuleException(msg)
  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)
  def symExecAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SymbolicExecutionError(msg)
}

