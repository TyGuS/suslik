package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.language.{Ident, Statements}
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis._
import org.tygus.synsl.logic.Unification._

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

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      // TODO: add value-returning statements
      val Goal(pre, post, _) = goal

      if (pre.sigma.isEmp &&
        post.sigma.isEmp &&
        post.phi.isTrue)
        List(Subderivation(Nil, _ => Skip))
      else Nil
    }
  }

  /*
           (GV(Q) / GV(P)) * GV(R) = Ø
          Γ ; {φ ; P} ; {ψ ; Q} ---> S
    ---------------------------------------- [*-intro]
      Γ ; {φ ; P * R} ; {ψ ; Q * R} ---> S


    This is the former [frame] rule
   */

  object StarIntro extends SynthesisRule {
    override def toString: String = "[Sub: *-intro]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      def sideCond(p: SFormula, q: SFormula, r: Heaplet) = {
        val gvP = p.vars.filter(goal.isGhost).toSet
        val gvQ = q.vars.filter(goal.isGhost).toSet
        val gvR = r.vars.filter(goal.isGhost)

        gvQ.diff(gvP).intersect(gvR).isEmpty
      }

      def findUnifyingHeaplets(pre: Assertion, post:Assertion): Option[(Assertion, Assertion)]  = {
        for (t <- pre.sigma.chunks) {
          for (s <- post.sigma.chunks) {
            tryUnify(t, s, goal.universals) match {
              case None =>
              case Some(sub) => {
                val newPreSigma = pre.sigma - t
                val newPostSigma = (post.sigma - s).subst(sub)
                val newPre = Assertion(pre.phi, newPreSigma)
                val newPost = Assertion(post.phi.subst(sub), newPostSigma)
                if (sideCond(newPreSigma, newPostSigma, t))
                  return Some((newPre, newPost))
              }
            }
          }
        }
        None
      }

      findUnifyingHeaplets(goal.pre, goal.post) match {
        case None => Nil
        case Some((newPre, newPost)) =>
          val newGoal = Goal(newPre, newPost, goal.gamma)
          List(Subderivation(List((newGoal, env)), pureKont(toString)))
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

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val Goal(pre, post, gamma: Gamma) = goal

      // Heaplet RHS has existentials
      def hasExistential: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.exists(v => goal.isExistential(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && hasExistential(hr)

      findMatchingHeaplets(_.isInstanceOf[PointsTo], isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@(PointsTo(x@Var(_), offset, e1)), hr@(PointsTo(_, _, e2)))) =>
          val cs = conjuncts(post.phi)
          if (cs.contains(PEq(e1, e2)) || cs.contains(PEq(e2, e1)))
            Nil
          else {
            val newPre = Assertion(pre.phi, goal.pre.sigma)
            val newPost = Assertion(mkConjunction(PEq(e1, e2) :: cs), goal.post.sigma)
            val newGoal = Goal(newPre, newPost, gamma)
            List(Subderivation(List((newGoal, env)), pureKont(toString)))
          }
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Pick rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }

  }

}
