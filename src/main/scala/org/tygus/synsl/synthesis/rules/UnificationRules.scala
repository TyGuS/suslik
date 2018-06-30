package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.LanguageUtils
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.Ident
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic.Specifications._
import org.tygus.synsl.logic.unification.{PureUnification, SpatialUnification}
import org.tygus.synsl.logic.unification.SpatialUnification.{FrameChoppingResult, tryUnify}
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis._

/**
  * The goal of unification rules is to eliminate existentials
  * via either heap unification or various forms of pure synthesis.
  * @author Nadia Polikarpova, Ilya Sergey
  */


object UnificationRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unification"

  abstract class HeapUnify extends SynthesisRule {
    def heapletFilter(h: Heaplet): Boolean

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post
      val deriv = goal.deriv

      val postCandidates = post.sigma.chunks.filter(p => p.vars.exists(goal.isExistential) && heapletFilter(p)).sortBy(_.rank)

      val alternatives = for {
        s <- postCandidates
        t <- pre.sigma.chunks.sortBy(_.rank)
        sub <- tryUnify(t, s, goal.universals, false)
        newPostSigma = post.sigma.subst(sub)
      } yield {
        val newPost = Assertion(post.phi.subst(sub), newPostSigma)

        val preFootprint = Set(deriv.preIndex.lastIndexOf(t))
        val postFootprint = Set(deriv.postIndex.lastIndexOf(s))
        val ruleApp = saveApplication((preFootprint, postFootprint), deriv)

        val newGoal = goal.copy(post = newPost, newRuleApp = Some(ruleApp))
        Subderivation(List(newGoal), pureKont(toString))
      }
//      nubBy[Subderivation,Assertion](sortAlternativesByFootprint(alternatives).toList, sub => sub.subgoals.head.post)
      nubBy[Subderivation,Assertion](alternatives, sub => sub.subgoals.head.post).sortBy(s => s.subgoals.head.distance)
    }
  }

  object HeapUnifyUnfolding extends HeapUnify with UnfoldingPhase  {
    override def toString: String = "[Sub: heap-unify-unfold]"
  }

  object HeapUnifyFlat extends HeapUnify with FlatPhase  {
    override def toString: String = "[Sub: heap-unify-flat]"
  }

  /*
    X ∈ GV(post) / GV (pre)
    Γ ; {φ ; P} ; {[l/X]ψ ; [l/X]Q} ---> S
    --------------------------------------- [subst-R]
    Γ ; {φ ; P} ; {ψ ∧ X = l; Q} ---> S
  */
  object SubstRight extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Norm: subst-R]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      def isExsistVar(e: Expr) = e.isInstanceOf[Var] && goal.isExistential(e.asInstanceOf[Var])

      findConjunctAndRest({
        case BinaryExpr(OpEq, l, r) => isExsistVar(l) || isExsistVar(r)
        // TODO [sets]: Can we enable this?
        case BinaryExpr(OpSetEq, l, r) => isExsistVar(l) || isExsistVar(r)
        case _ => false
      }, simplify(p2)) match {
        case Some((BinaryExpr(_, l, r), rest2)) =>
          val (x, e) = if (isExsistVar(l)) {
            (l.asInstanceOf[Var], r)
          } else {
            (r.asInstanceOf[Var], l)
          }
          val _p2 = simplify(mkConjunction(rest2).subst(x, e))
          val _s2 = s2.subst(x, e)
          val newGoal = goal.copy(post = Assertion(_p2, _s2))
          List(Subderivation(List(newGoal), pureKont(toString)))
        case _ => Nil
      }
    }
  }

  /*
     Γ ; {φ ∧ φ1 ; P} ; {ψ' ; Q'} ---> S
             s = unify(φ1, φ2)
       {ψ' ; Q'} = subst({ψ ; Q}, s)
   --------------------------------------- [Pure-Unify]
   Γ ; {φ ∧ φ1 ; P} ; {ψ ∧ φ2 ; Q} ---> S

    */

  object PureUnify extends SynthesisRule with FlatPhase {
    override def toString: String = "[Norm: pure-unify]"

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
    Γ, l ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l * Q}[l/m] ---> S   m is existential
  --------------------------------------------------------------------------------[pick-from-env]
     Γ ; {φ ; x.f -> - * P} ; {ψ ; x.f -> m * Q} ---> *x.f := l ; S
   */
  object PickFromEnvRule extends SynthesisRule with FlatPhase with InvertibleRule {

    override def toString: Ident = "[Op: write-from-env]"

    def apply(goal: Goal): Seq[Subderivation] = {

      val pre = goal.pre
      val post = goal.post

      def isSuitable: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, v@Var(_)) =>
          !goal.isGhost(x) && goal.isExistential(v) && LanguageUtils.isNotDefaultFreshVar(v)
        case _ => false
      }

      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && isSuitable(hr)

      if (post.sigma.chunks.size > 1) return Nil

      findMatchingHeaplets(noGhosts, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@PointsTo(x@Var(_), offset, _), hr@PointsTo(_, _, m@Var(_)))) =>
          for {
            // Try variables from the context
            l <- goal.programVars.toList
            newPre = Assertion(pre.phi, (goal.pre.sigma - hl) ** PointsTo(x, offset, l))
            subGoal = goal.copy(newPre, post.subst(m, l))
            kont = (stmts: Seq[Statement]) => {
              ruleAssert(stmts.lengthCompare(1) == 0, s"Write rule expected 1 premise and got ${stmts.length}")
              val rest = stmts.head
              SeqComp(Store(x, offset, l), rest)
            }
          } yield Subderivation(List(subGoal), kont)
        case Some((hl, hr)) =>
          ruleAssert(false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }
  }

  /*
      Γ ; {φ ; x.f -> l * P} ; {ψ ∧ Y = l ; x.f -> Y * Q} ---> S
      ---------------------------------------------------------- [pick]
      Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> Y * Q} ---> S
   */

  object Pick extends SynthesisRule with FlatPhase {
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

  /*
           (GV(Post) / GV(Pre)) * GV(R) = Ø
          Γ ; {φ ; P} ; {ψ ; Q} ---> S
    ---------------------------------------- [*-intro]
      Γ ; {φ ; P * R} ; {ψ ; Q * R} ---> S


    This is the former [frame] rule
   */

  object StarIntro extends SynthesisRule with AnyPhase {
    override def toString: String = "[Sub: *-intro]"

    def apply(goal: Goal): Seq[Subderivation] = {

      val pre = goal.pre
      val post = goal.post
      val boundVars = goal.universals
      val deriv = goal.deriv
      val foundFrames = SpatialUnification.removeCommonFrame(post.sigma, pre.sigma, boundVars)
      val alternatives = for {
        FrameChoppingResult(newPostSigma, postFrame, newPreSigma, preFrame, sub) <- foundFrames

        newPre = Assertion(pre.phi, newPreSigma)
        newPost = Assertion(post.phi.subst(sub), newPostSigma)
        preFootprint = preFrame.chunks.map(p => deriv.preIndex.lastIndexOf(p)).toSet
        postFootprint = postFrame.chunks.map(p => deriv.postIndex.lastIndexOf(p)).toSet
        ruleApp = saveApplication((preFootprint, postFootprint), deriv)
        newGoal = goal.copy(newPre, newPost, newRuleApp = Some(ruleApp))
      } yield {
        Subderivation(List(newGoal), pureKont(toString))
      }
      sortAlternativesByFootprint(alternatives)    }
  }

}
