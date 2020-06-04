package org.tygus.suslik.certification.targets.coq.logic.rules

import org.tygus.suslik.certification.targets.coq.logic.Proof._
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp

object LogicalRules {
  case class CEmpApp(env: CEnvironment) extends CRuleApp(env) {
    override def fn(steps: Seq[String]): String =
      "ssl_emp.\n" + steps.headOption.getOrElse("")
  }
}
