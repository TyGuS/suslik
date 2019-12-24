package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.SSLException

/**
  * @author Ilya Sergey
  */

trait RuleUtils {

  val exceptionQualifier: String

  case class SynthesisRuleException(msg: String) extends SSLException(exceptionQualifier, msg)

  def ruleAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisRuleException(msg)
}

