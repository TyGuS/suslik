package org.tygus.suslik.certification.targets.coq.logic.rules

import org.tygus.suslik.certification.targets.coq.language.Expressions.CVar
import org.tygus.suslik.certification.targets.coq.logic.Proof._

object Rules {
  abstract class CRuleApp(env: CEnvironment) {
    val nextEnvs: Seq[CEnvironment] = Seq(env.copy())

    // whether this should appear as an explicit proof step in the Coq script
    val isExplicit: Boolean = true

    def fn(steps: Seq[String]): String = steps.headOption.getOrElse("")

    protected def nestedDestruct(items: Seq[CVar]): String = items.toList match {
      case v1 :: v2 :: rest =>
        s"[${v1.pp} ${nestedDestruct(v2 :: rest)}]"
      case v :: _ =>
        v.pp
      case Nil =>
        ""
    }

  }
}
