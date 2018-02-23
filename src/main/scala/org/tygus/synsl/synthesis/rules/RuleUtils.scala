package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.SynSLException
import org.tygus.synsl.synthesis.StmtProducer
import org.tygus.synsl.synthesis.rules.SubtractionRules.ruleAssert

/**
  * @author Ilya Sergey
  */

trait RuleUtils {

  val exceptionQualifier: String

  case class SynthesisRuleException(msg: String) extends SynSLException(exceptionQualifier, msg)

  protected[synthesis] def ruleAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisRuleException(msg)

  def pureKont(rulename: String): StmtProducer =
    stmts => {
      ruleAssert(stmts.lengthCompare(1) == 0, s"Rule $rulename expects 1 premise and got ${stmts.length}")
      stmts.head
    }

}
