package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.SynSLException
import org.tygus.synsl.synthesis.{StmtProducer, Subderivation}

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

  // Sort a sequence of alternative subderivations (where every subderivation contains a single goal)
  // by the footprint of their latest rule application,
  // so that sequential applications of the rule are unlikely to cause out-of-order derivations
  def sortAlternativesByFootprint(alts: Seq[Subderivation]): Seq[Subderivation] = {
    alts.sortBy(_.subgoals.head._1.deriv.applications.head)
  }
}
