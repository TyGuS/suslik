package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.SynSLException

/**
  * @author Ilya Sergey
  */

trait RuleUtils {

  val exceptionQualifier : String

  case class SynthesisRuleException(msg: String) extends SynSLException(exceptionQualifier, msg)

  protected[synthesis] def ruleAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisRuleException(msg)

}
