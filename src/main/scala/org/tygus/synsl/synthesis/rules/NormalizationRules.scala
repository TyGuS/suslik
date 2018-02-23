package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis.rules.SubtractionRules.pureKont
import org.tygus.synsl.synthesis.{SynFail, SynMoreGoals, SynthesisRule, SynthesisRuleResult}

/**
  * @author Ilya Sergey
  */

object NormalizationRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-normalization"

  // TODO: Implement [=-R]
  // TODO: Implement [subst-R]
  // TODO: Implement [subst-L]
  // TODO: Implement [=-L]
  // TODO: Implement [inconsistency]

  // TODO: Implement [nil-not-lval]
  // TODO: Implement [*-partial]

  /*

  Γ ; {φ ∧ φ' ; P} ; {ψ ; Q} ---> S
  --------------------------------------- [Hypothesis]
  Γ ; {φ ∧ φ' ; P} ; {ψ ∧ φ' ; Q} ---> S

  */
  object Hypothesis extends SynthesisRule {
    override def toString: String = "[Norm: Hypothesis]"
    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      (conjuncts(spec.pre.phi), conjuncts(spec.post.phi)) match {
        case (Some(cs1), Some(cs2)) =>
          findCommon((p: PFormula) => true, cs1, cs2) match {
            case Some((p, ps1, ps2)) =>
              val newPost = Assertion(mkConjunction(ps2), spec.post.sigma)
              val newSpec = Spec(spec.pre, newPost, spec.gamma)
              SynMoreGoals(List(newSpec), pureKont(toString))
            case None => SynFail
          }
        case _ => SynFail
      }
    }
  }

}
