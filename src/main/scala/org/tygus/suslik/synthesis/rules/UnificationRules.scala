package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.LanguageUtils
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{Ident, IntType}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.unification.{PureUnification}
import org.tygus.suslik.logic.unification.SpatialUnification.tryUnify
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * The goal of unification rules is to eliminate existentials
  * via either heap unification or various forms of pure synthesis.
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */


object UnificationRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unification"

  abstract class HeapUnify extends SynthesisRule {
    def heapletFilter(h: Heaplet): Boolean

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post
      val deriv = goal.hist

      val postCandidates = post.sigma.chunks.filter(p => p.vars.exists(goal.isExistential) && heapletFilter(p)).sortBy(_.rank)

      def sort(chunks: List[Heaplet]): List[Heaplet] = {

        val flags = goal.env.config.flags

        // RANK (default)
        if (flags(0))
          chunks.sortBy(_.rank)

        // RANK (desc)
        else if (flags(1))
          chunks.sortBy(-_.rank)

        //  SIZE:
        else if (flags(2))
          chunks.sortBy(_.size)

        //  SIZE (desc):
        else if (flags(3))
          chunks.sortBy(-_.size)

        //  COST:
        else if (flags(4))
          chunks.sortBy(_.cost)

        //  COST (desc):
        else if (flags(5))
          chunks.sortBy(-_.cost)

        // points-to ; sapp
        else if (flags(6))
          chunks.sortBy(_.name)

        // sapp ; pointsto
        else if (flags(7))
          chunks.sortBy(_.name).reverse

        else chunks.sortBy(_.rank)
      }


      val alternatives = for {
        s <- postCandidates
        // at least one eval flag is set
        t <- if (goal.env.config.flags.contains(true)) sort(pre.sigma.chunks)
        else pre.sigma.chunks.sortBy(_.rank)
        // TODO create appropriate substitutions
        sub <- {
          tryUnify(t, s, goal.universals, tagsMatter = false, _ == _)
        }
        newPostSigma = post.sigma.subst(sub)
      } yield {
        val newPost = Assertion(post.phi.subst(sub), newPostSigma)

        val preFootprint = Set(deriv.preIndex.lastIndexOf(t))
        val postFootprint = Set(deriv.postIndex.lastIndexOf(s))
        val ruleApp = saveApplication((preFootprint, postFootprint), deriv, -pre.similarity(newPost))
        val newGoal = goal.spawnChild(post = newPost, newRuleApp = Some(ruleApp))
        val kont = idProducer >> handleGuard(goal) >> extractHelper(goal)
        (RuleResult(List(newGoal), kont, toString), t.rank)
      }
      //      nubBy[Subderivation,Assertion](sortAlternativesByFootprint(alternatives).toList, sub => sub.subgoals.head.post)
      val ord = new Ordering[(Int, Int, RuleApplication)] {
        def compare(x: (Int, Int, RuleApplication), y: (Int, Int, RuleApplication)): Int = {
          val c1 = x._1.compare(y._1)
          if (c1 != 0) c1
          else {
            val c2 = x._2.compare(y._2)
            //TODO [immutability] enable/disable imm sensitive cost (just a hack, to upgrade it to rule if it has impact)
            if (c2 != 0 && goal.env.config.prioImm) c2
            else x._3.compare(y._3)
          }
        }
      }
      val derivations = nubBy[(RuleResult, Int), Assertion](alternatives, sub => sub._1.subgoals.head.post)
      val derivations_s = if (goal.env.config.flags.contains(true)) derivations
      else derivations.sortBy(s => (-s._1.subgoals.head.similarity, s._2, s._1.subgoals.head.hist.applications.head))(ord)
      val (res_derivations, _) = derivations_s.unzip
      res_derivations
    }
  }

  object HeapUnifyUnfolding extends HeapUnify with UnfoldingPhase {
    override def toString: String = "HeapUnifyUnfold"
  }

  object HeapUnifyFlat extends HeapUnify with FlatPhase {
    override def toString: String = "HeapUnifyFlat"
  }

  /*
    X ∈ GV(post) / GV (pre)
    Γ ; {φ ; P} ; {[l/X]ψ ; [l/X]Q} ---> S
    --------------------------------------- [subst-R]
    Γ ; {φ ; P} ; {ψ ∧ X = l; Q} ---> S
  */
  object SubstRight extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "SubstR"

    def apply(goal: Goal): Seq[RuleResult] = {
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      def isExsistVar(e: Expr) = e.isInstanceOf[Var] && goal.isExistential(e.asInstanceOf[Var])

      findConjunctAndRest({
        case BinaryExpr(OpEq, l, r) => isExsistVar(l) || isExsistVar(r)
        // TODO: discuss and enable
        //        case BinaryExpr(OpBoolEq, l, r) => isExsistVar(l) || isExsistVar(r)
        // TODO [sets]: Can we enable this?
        case BinaryExpr(OpSetEq, l, r) => isExsistVar(l) || isExsistVar(r)
        case _ => false
      }, p2) match {
        case Some((BinaryExpr(_, l, r), rest2)) =>
          val (x, e) = if (isExsistVar(l)) {
            (l.asInstanceOf[Var], r)
          } else {
            (r.asInstanceOf[Var], l)
          }
          val _p2 = mkConjunction(rest2).subst(x, e)
          val _s2 = s2.subst(x, e)
          val newGoal = goal.spawnChild(post = Assertion(_p2, _s2))
          val kont = idProducer >> handleGuard(goal) >> extractHelper(goal)
          List(RuleResult(List(newGoal), kont, toString))
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
    override def toString: String = "PureUnify"

    def apply(goal: Goal): Seq[RuleResult] = {
      // get post conjuncts with existentials
      val postConjuncts = goal.post.phi.conjuncts.filter(p => p.vars.exists(goal.isExistential) && p.allowUnify)
      val preConjuncts = goal.pre.phi.conjuncts.filter(p => p.allowUnify)

      for {
        s <- postConjuncts
        t <- preConjuncts
        sigma <- PureUnification.tryUnify(t, s, goal.existentials)
        newGoal = goal.spawnChild(post = goal.post.subst(sigma))
        kont = idProducer >> handleGuard(goal) >> extractHelper(goal)
      } yield RuleResult(List(newGoal), kont, toString)
    }
  }

  /*
    Γ, l ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l * Q}[l/m] ---> S   m is existential
  --------------------------------------------------------------------------------[pick-from-env]
     Γ ; {φ ; x.f -> - * P} ; {ψ ; x.f -> m * Q} ---> *x.f := l ; S
   */
  object PickFromEnvRule extends SynthesisRule with FlatPhase with InvertibleRule {

    override def toString: Ident = "WriteFromEnv"

    def apply(goal: Goal): Seq[RuleResult] = {

      val pre = goal.pre
      val post = goal.post

      def isSuitable: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, v@Var(_), _) =>
          !goal.isGhost(x) && goal.isExistential(v) && LanguageUtils.isNotDefaultFreshVar(v)
        case _ => false
      }

      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e, _) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && isSuitable(hr)

      if (post.sigma.chunks.size > 1) return Nil

      findMatchingHeaplets(noGhosts, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@PointsTo(x@Var(_), offset, _, _), hr@PointsTo(_, _, m@Var(_), _))) =>
          for {
            // Try variables from the context
            l <- goal.programVars.toList
            if goal.gamma(l).conformsTo(Some(IntType))
            newPre = Assertion(pre.phi, (goal.pre.sigma - hl) ** PointsTo(x, offset, l))
            subGoal = goal.spawnChild(newPre, post.subst(m, l))
            kont = prepend(Store(x, offset, l)) >> handleGuard(goal) >> extractHelper(goal)
          } yield RuleResult(List(subGoal), kont, toString)
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
    override def toString: String = "Pick"

    def apply(goal: Goal): Seq[RuleResult] = {

      if (goal.pre.sigma.isEmp && goal.post.sigma.isEmp) {
        // This is a rule of last resort so only apply when heaps are empty
        for {
          ex <- goal.existentials.toList
          v <- goal.universals.toList
          if goal.getType(ex).conformsTo(Some(goal.getType(v)))
          sigma = Map(ex -> v)
          newGoal = goal.spawnChild(post = goal.post.subst(sigma))
          kont = idProducer >> handleGuard(goal) >> extractHelper(goal)
        } yield RuleResult(List(newGoal), kont, toString)
      } else Nil
    }
  }

}
