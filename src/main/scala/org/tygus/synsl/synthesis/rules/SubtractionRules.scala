package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.{Ident, IntSetType, Statements}
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.Specifications._
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.logic.unification.SpatialUnification.{FrameChoppingResult, tryUnify}
import org.tygus.synsl.logic.unification.{PureUnification, SpatialUnification}
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

  object EmpRule extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "[Sub: emp]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post

      if (pre.sigma.isEmp && post.sigma.isEmp) { // heaps are empty
        val (eConjuncts, neConjuncts) = conjuncts(post.phi).partition(p => p.vars.exists(goal.isExistential))
        if (eConjuncts.isEmpty) { // no existentials
          if (SMTSolving.valid(pre.phi ==> post.phi))
            List(Subderivation(Nil, _ => Skip)) // pre implies post: we are done
          else
            List(Subderivation(Nil, _ => Magic)) // pre doesn't imply post: only magic can save us
        } else { // has existentials: check if the rest of the post is already invalid
          if (SMTSolving.valid(pre.phi ==> mkConjunction(neConjuncts)))
            Nil // valid so far, nothing to say
          else
            List(Subderivation(Nil, _ => Magic)) // pre doesn't imply even a weaker post: only magic can save us
        }
      } else Nil // heaps non-empty
    }
  }

  /*
           (GV(Post) / GV(Pre)) * GV(R) = Ø
          Γ ; {φ ; P} ; {ψ ; Q} ---> S
    ---------------------------------------- [*-intro]
      Γ ; {φ ; P * R} ; {ψ ; Q * R} ---> S


    This is the former [frame] rule
   */

  object StarIntro extends SynthesisRule {
    override def toString: String = "[Sub: *-intro]"

    def apply(goal: Goal): Seq[Subderivation] = {

      def ghostEqualities(newGoal: Goal): PFormula = {
        val conjuncts = for (v <- newGoal.existentials -- goal.existentials)
          yield newGoal.getType(v) match {
            case IntSetType => BinaryExpr(OpSetEq, v, v)
            case _ =>  v |=| v
          }
        mkConjunction(conjuncts.toList)
      }


      val pre = goal.pre
      val post = goal.post
      val boundVars = goal.universals
      val deriv = goal.deriv
      val foundFrames = SpatialUnification.removeCommonFrame(post.sigma, pre.sigma, boundVars)
      val alternatives = for {
        FrameChoppingResult(newPostSigma, postFrame, newPreSigma, preFrame, sub) <- foundFrames

        newPre = Assertion(pre.phi, newPreSigma)
        newPost = Assertion(post.phi.subst(sub), newPostSigma)
        preFootprint = preFrame.chunks.map(p => deriv.preIndex.indexOf(p)).toSet
        postFootprint = postFrame.chunks.map(p => deriv.postIndex.indexOf(p)).toSet
        ruleApp = saveApplication((preFootprint, postFootprint), deriv)
        tempGoal = goal.copy(newPre, newPost, newRuleApp = Some(ruleApp))
        newPreAdjusted = newPre.copy(phi = andClean(newPre.phi, ghostEqualities(tempGoal)))
        newGoal = tempGoal.copy(pre = newPreAdjusted)
        if newGoal.existentials.subsetOf(goal.existentials)
      } yield {
        Subderivation(List(newGoal), pureKont(toString))
      }
      sortAlternativesByFootprint(alternatives)    }
  }


  object StarIntroOld extends SynthesisRule {
    override def toString: String = "[Sub: *-intro]"

    def apply(goal: Goal): Seq[Subderivation] = {
      def sideCond(p: SFormula, q: SFormula, r: Heaplet) = {
        val gvP = p.vars.filter(goal.isGhost).toSet
        val gvQ = q.vars.filter(goal.isGhost).toSet
        val gvR = r.vars.filter(goal.isGhost)

        gvQ.diff(gvP).intersect(gvR).isEmpty
      }

      val pre = goal.pre
      val post = goal.post
      val deriv = goal.deriv

      val alternatives = for {
        t <- pre.sigma.chunks
        s <- post.sigma.chunks
        sub <- tryUnify(t, s, goal.universals, false)
        newPreSigma = pre.sigma - t
        newPostSigma = (post.sigma - s).subst(sub)
        if sideCond(newPreSigma, newPostSigma, t)
      } yield {
        val newPre = Assertion(pre.phi, newPreSigma)
        val newPost = Assertion(post.phi.subst(sub), newPostSigma)

        val preFootprint = Set(deriv.preIndex.indexOf(t))
        val postFootprint = Set(deriv.postIndex.indexOf(s))
        val ruleApp = saveApplication((preFootprint, postFootprint), deriv)

        val newGoal = goal.copy(newPre, newPost, newRuleApp = Some(ruleApp))
        Subderivation(List(newGoal), pureKont(toString))
      }
      sortAlternativesByFootprint(alternatives)
    }
  }


  /*
    Γ ; {φ ∧ φ1 ; P} ; {ψ' ; Q'} ---> S
            s = unify(φ1, φ2)
      {ψ' ; Q'} = subst({ψ ; Q}, s)
  --------------------------------------- [Hypothesis-Unify]
  Γ ; {φ ∧ φ1 ; P} ; {ψ ∧ φ2 ; Q} ---> S

   */

  object HypothesisUnify extends SynthesisRule {
    override def toString: String = "[Sub: hypothesis-unify]"

    def apply(goal: Goal): Seq[Subderivation] = {
      // get post conjuncts with existentials
      val postConjuncts = conjuncts(goal.post.phi).filter(p => p.vars.exists(goal.isExistential))
      val preConjuncts = conjuncts(goal.pre.phi)

      for {
        s <- postConjuncts
        t <- preConjuncts
        sigma <- PureUnification.tryUnify(t, s, goal.existentials)
        newGoal = goal.copy(post = goal.post.subst(sigma))
      } yield Subderivation(List(newGoal), pureKont(toString))
    }
  }


  /*
      Γ ; {φ ; x.f -> l * P} ; {ψ ∧ Y = l ; x.f -> Y * Q} ---> S
      ---------------------------------------------------------- [pick]
      Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> Y * Q} ---> S
   */

  object Pick extends SynthesisRule {
    override def toString: String = "[Sub: pick]"

    def apply(goal: Goal): Seq[Subderivation] = {

      if (goal.pre.sigma.isEmp && goal.post.sigma.isEmp) {
        // This is a rule of last resort so only apply when heaps are empty
        for {
          ex <- goal.existentials.toList
          v <- goal.universals.toList
          if goal.getType(ex).conformsTo(Some(goal.getType(v)))
          sigma = Map(ex -> v)
          newGoal = goal.copy(post = goal.post.subst(sigma))
        } yield Subderivation(List(newGoal), pureKont(toString))
      } else Nil
    }
  }

}
