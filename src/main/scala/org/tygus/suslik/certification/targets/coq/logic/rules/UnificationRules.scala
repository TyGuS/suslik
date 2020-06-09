package org.tygus.suslik.certification.targets.coq.logic.rules

import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.logic.Proof.CEnvironment
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp

object UnificationRules {
  case class CPickApp(subst: Map[CVar, CExpr], env: CEnvironment) extends CRuleApp(env) {
    override val nextEnvs: Seq[CEnvironment] = Seq(env.copy(existentials = env.existentials ++ subst))
    override val isExplicit: Boolean = false
  }
}
