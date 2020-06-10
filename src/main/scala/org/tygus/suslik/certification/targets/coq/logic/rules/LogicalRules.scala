package org.tygus.suslik.certification.targets.coq.logic.rules

import org.tygus.suslik.certification.targets.coq.logic.Proof._
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp

object LogicalRules {
  case class CEmpApp(env: CEnvironment) extends CRuleApp(env) {
    override def fn(steps: Seq[String]): String = {
      val builder = new StringBuilder()
      builder.append("ssl_emp;\n")

      // instantiate any existentials from the fun spec post
      val postEx = {
        (env.spec.post.pureEx ++ env.spec.post.spatialEx ++ env.spec.post.heapEx).diff(env.spec.programVars).distinct
      }
      if (postEx.nonEmpty) {
        val postExSubs = postEx.map(e => env.existentials(e).pp)
        builder.append(s"exists ${postExSubs.mkString(", ")};\n")
      }

      builder.append("ssl_emp_post.\n")
      steps.headOption.map(builder.append)
      builder.toString()
    }
  }
}
