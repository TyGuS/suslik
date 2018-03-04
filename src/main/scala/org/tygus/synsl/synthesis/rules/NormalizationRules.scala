package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.language.Statements.Skip
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis._

/**
  * @author Ilya Sergey
  */

object NormalizationRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-normalization"

  // TODO: Implement [subst-R]

  // TODO: Implement [nil-not-lval]
  // TODO: Implement [*-partial]

  /*
  Γ ; {[l/x]φ ; [l/x]P} ; {[l/x]ψ ; [l/x]Q} ---> S
  ------------------------------------------------ [subst-L]
  Γ ; {φ ∧ x = l ; P} ; {ψ ; Q} ---> S
  */
  object SubstLeft extends SynthesisRule {
    override def toString: String = "[Norm: Substitution]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(Assertion(p1, s1), Assertion(p2, s2), g) = spec

      findConjunctAndRest({
        case PEq(v1@Var(_), v2) => v1 != v2
        case _ => false
      }, simplify(p1)) match {
        case Some((PEq(x@Var(_), l), rest1)) =>
          val _p1 = mkConjunction(rest1).subst(x, l)
          val _s1 = s1.subst(x, l)
          val _p2 = p2.subst(x, l)
          val _s2 = s2.subst(x, l)
          val newSpec = Spec(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2),
            g.filter { case (t, w) => w != x })
          SynMoreGoals(List(newSpec), pureKont(toString))
        case _ => SynFail
      }
    }
  }

  /*
  Γ ; {φ ; P} ; {ψ ; Q} ---> S
  -------------------------------------- [=-L]
  Γ ; {φ ∧ l = l ; P} ; {ψ ; Q} ---> S
  */
  object StripEqPre extends SynthesisRule {
    override def toString: String = "[Norm: =-L]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      findConjunctAndRest({
        case PEq(x, y) => x == y
        case _ => false
      }, simplify(spec.pre.phi)) match {
        case None => SynFail
        case Some((_, rest)) =>
          val newPre = Assertion(mkConjunction(rest), spec.pre.sigma)
          val newSpec = Spec(newPre, spec.post, spec.gamma)
          SynMoreGoals(List(newSpec), pureKont(toString))
      }
    }
  }

  /*
  --------------------------------------- [inconsistency]
  Γ ; {φ ∧ l ≠ l ; P} ; {ψ ; Q} ---> emp
  */
  object Inconsistency extends SynthesisRule {
    override def toString: String = "[Norm: Inconsistency]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(Assertion(p1, _), _, g) = spec
      val res = findConjunctAndRest({
        case PNeg(PEq(x, y)) => x == y
        case _ => false
      }, simplify(p1))
      res match {
        case Some((PNeg(PEq(x, y)), rest1)) if x == y =>
          SynMoreGoals(Nil, _ => Skip)
        case _ => SynFail
      }
    }
  }


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


  /*

  Γ ; {φ ; P} ; {ψ ; Q} ---> S
  ------------------------------------- [=-R]
  Γ ; {φ ; P} ; {ψ ∧ l = l ; Q} ---> S

   */
  object StripEqPost extends SynthesisRule {
    override def toString: String = "[Sub: =-R]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      findConjunctAndRest({
        case PEq(x, y) => x == y
        case _ => false
      }, simplify(spec.post.phi)) match {
        case None => SynFail
        case Some((_, rest)) =>
          val newPost = Assertion(mkConjunction(rest), spec.post.sigma)
          val newSpec = Spec(spec.pre, newPost, spec.gamma)
          SynMoreGoals(List(newSpec), pureKont(toString))
      }
    }
  }


}
