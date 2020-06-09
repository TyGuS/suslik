package org.tygus.suslik.certification.targets.coq.logic.rules

import org.tygus.suslik.certification.targets.coq.language.Expressions.CExpr
import org.tygus.suslik.certification.targets.coq.logic.Proof.CEnvironment
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp

object FailRules {
  case class CAbduceBranchApp(cond: CExpr, env: CEnvironment) extends CRuleApp(env) {
    override val nextEnvs: Seq[CEnvironment] = Seq(env, env)

    override def fn(steps: Seq[String]): String = {
      val builder = new StringBuilder()
      builder.append("case: ifP=>H_cond.\n")
      steps.foreach(builder.append)
      builder.append("\n")
      builder.toString()
    }
  }
}
