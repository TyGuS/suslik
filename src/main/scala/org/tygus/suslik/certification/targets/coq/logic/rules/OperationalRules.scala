package org.tygus.suslik.certification.targets.coq.logic.rules

import org.tygus.suslik.certification.targets.coq.language.Expressions.CVar
import org.tygus.suslik.certification.targets.coq.logic.Proof._
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp

object OperationalRules {
  case class CWriteApp(to: CVar, env: CEnvironment) extends CRuleApp(env) {
    override def fn(steps: Seq[String]): String =
      s"ssl_write.\nssl_write_post ${to.pp}.\n" + steps.headOption.getOrElse("")
  }

  case class CReadApp(env: CEnvironment) extends CRuleApp(env) {
    override def fn(steps: Seq[String]): String =
      "ssl_read.\n" + steps.headOption.getOrElse("")
  }

  case class CFreeApp(size: Int, env: CEnvironment) extends CRuleApp(env) {
    override def fn(steps: Seq[String]): String = {
      val deallocStmts = (1 to size).map(_ => "ssl_dealloc.")
      s"${deallocStmts.mkString("\n")}\n" + steps.headOption.getOrElse("")
    }
  }
}
