package org.tygus.synsl.synthesis.rules

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
        SynMoreGoals(Nil, _ => Skip)
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
        ((gvQ -- gvP) ++ gvR).isEmpty
      }

      findCommon(Function.const(true), cs1, cs2) match {
        case Some((r, p, q)) if sideCond(SFormula(p), SFormula(q), SFormula(List(r))) =>
          val newPre = Assertion(spec.pre.phi, SFormula(p))
          val newPost = Assertion(spec.post.phi, SFormula(q))
          val newSpec = Spec(newPre, newPost, spec.gamma)
          SynMoreGoals(List(newSpec), pureKont(toString))
        case _ => SynFail
      }
    }
  }

}
