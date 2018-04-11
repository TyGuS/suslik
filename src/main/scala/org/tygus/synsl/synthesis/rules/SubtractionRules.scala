package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.language.{Ident, Statements}
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis._

/**
  * @author Ilya Sergey
  */

object SubtractionRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-subtraction"

  import Statements._

  /*

    -------------------------------- [emp]
    Γ ; {φ ; emp} ; {emp} ---> skip

  Empty rule: supposed to be applied at the end

  */

  object EmpRule extends SynthesisRule {

    override def toString: Ident = "[Sub: emp]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      // TODO: add value-returning statements
      val Spec(pre, post, _) = spec

      if (pre.sigma.isEmp &&
          post.sigma.isEmp &&
          post.phi.isTrue)
        SynAndGoals(Nil, _ => Skip)
      else SynFail
    }
  }

  /*
           (GV(Q) / GV(P)) ∪ GV(R) = Ø
          Γ ; {φ ; P} ; {ψ ; Q} ---> S
    ---------------------------------------- [*-intro]
      Γ ; {φ ; P * R} ; {ψ ; Q * R} ---> S


    This is the former [frame] rule
   */

  object StarIntro extends SynthesisRule {
    override def toString: String = "[Sub: *-intro]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val cs1 = spec.pre.sigma.chunks
      val cs2 = spec.post.sigma.chunks

      def sideCond(p: SFormula, q: SFormula, r: SFormula) = {
        val gvP = p.vars.filter(spec.isGhost).toSet
        val gvQ = q.vars.filter(spec.isGhost).toSet
        val gvR = r.vars.filter(spec.isGhost).toSet

        (gvP ++ gvQ).intersect(gvR).isEmpty
      }

      findCommon(Function.const(true), cs1, cs2) match {
        case Some((r, p, q)) if sideCond(SFormula(p), SFormula(q), SFormula(List(r))) =>
          val newPre = Assertion(spec.pre.phi, SFormula(p))
          val newPost = Assertion(spec.post.phi, SFormula(q))
          val newSpec = Spec(newPre, newPost, spec.gamma)
          SynAndGoals(List(newSpec), pureKont(toString))
        case _ => SynFail
      }
    }
  }


  /*
      Γ ; {φ ; x.f -> l * P} ; {ψ ∧ Y = l ; x.f -> Y * Q} ---> S
      ---------------------------------------------------------- [pick]
      Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> Y * Q} ---> S
   */

  object Pick extends SynthesisRule {
    override def toString: String = "[Sub: pick]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      // Heaplet RHS has existentials
      def hasExistential: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.exists(v => spec.isExistential(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && hasExistential(hr)

      findMatchingHeaplets(_.isInstanceOf[PointsTo], isMatch, spec.pre.sigma, spec.post.sigma) match {
        case None => SynFail
        case Some((hl@(PointsTo(x@Var(_), offset, e1)), hr@(PointsTo(_, _, e2)))) =>
          conjuncts(post.phi) match {
            case None => SynFail
            case Some(cs) =>
              if (cs.contains(PEq(e1, e2)) || cs.contains(PEq(e2, e1)))
                SynFail
              else {
                val newPre = Assertion(pre.phi, spec.pre.sigma)
                val newPost = Assertion(mkConjunction(PEq(e1, e2) :: cs), spec.post.sigma)
                val newSpec = Spec(newPre, newPost, gamma)
                SynAndGoals(List(newSpec), pureKont(toString))
              }
          }
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Pick rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          SynFail
      }
    }

  }

}
