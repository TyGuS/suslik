package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.LanguageUtils
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.{Ident, IntType}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.unification.PureUnification
import org.tygus.suslik.logic.unification.SpatialUnification
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

    def varFilter(h: Heaplet, v: Var): Boolean = true

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      val postCandidates = post.sigma.chunks.filter(p => p.vars.exists(goal.isExistential) && heapletFilter(p))

      val alternatives = for {
        s <- postCandidates
        t <- pre.sigma.chunks
        wholeSub <- SpatialUnification.tryUnify(t, s, goal.universals)
        sub = wholeSub.filterKeys(v => varFilter(s, v))
        if sub.nonEmpty
        newPostSigma = post.sigma.subst(sub)
        if newPostSigma.chunks.distinct.size == newPostSigma.chunks.size // discard substituion if is produces duplicate chunks in the post
      } yield {
        val newPost = Assertion(post.phi.subst(sub), newPostSigma)

        val newGoal = goal.spawnChild(post = newPost)
        val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
        RuleResult(List(newGoal), kont, goal.allHeaplets - newGoal.allHeaplets + Footprint(singletonHeap(t), emp), this)
      }
      val derivations = nubBy[RuleResult, Assertion](alternatives, sub => sub.subgoals.head.post)
      derivations.sortBy(s => -s.subgoals.head.similarity)
    }
  }

  object HeapUnifyUnfolding extends HeapUnify with UnfoldingPhase {
    override def toString: String = "HeapUnifyUnfold"
  }

  object HeapUnifyBlock extends HeapUnify with BlockPhase {
    override def toString: String = "HeapUnifyBlock"
  }

  object HeapUnifyPointer extends HeapUnify with FlatPhase {
    override def toString: String = "HeapUnifyPointer"

    override def varFilter(h: Heaplet, v: Var): Boolean = h match {
      case PointsTo(x, _, _) => v == x
      case _ => false
    }
  }

  object HeapUnifyPure extends HeapUnify with FlatPhase {
    override def toString: String = "HeapUnifyPure"
  }

  /*
    X ∈ GV(post) / GV (pre)
    Γ ; {φ ; P} ; {[l/X]ψ ; [l/X]Q} ---> S
    --------------------------------------- [subst-R]
    Γ ; {φ ; P} ; {ψ ∧ X = l; Q} ---> S
  */
  object SubstRight extends SynthesisRule with InvertibleRule {
    override def toString: String = "SubstR"

    def apply(goal: Goal): Seq[RuleResult] = {
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      def isExsistVar(e: Expr) = e.isInstanceOf[Var] && goal.isExistential(e.asInstanceOf[Var])

      findConjunctAndRest({
        case BinaryExpr(OpEq, l, r) => isExsistVar(l) || isExsistVar(r)
          // TODO: discuss and enable
//        case BinaryExpr(OpBoolEq, l, r) => isExsistVar(l) || isExsistVar(r)
        case BinaryExpr(OpSetEq, l, r) => isExsistVar(l) || isExsistVar(r)
        case _ => false
      }, p2) match {
        case Some((BinaryExpr(_, l, r), rest2)) =>
          val (x, e) = if (isExsistVar(l)) {
            (l.asInstanceOf[Var], r)
          } else {
            (r.asInstanceOf[Var], l)
          }
          val _p2 = rest2.subst(x, e)
          val _s2 = s2.subst(x, e)
          val newGoal = goal.spawnChild(post = Assertion(_p2, _s2))
          val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
          List(RuleResult(List(newGoal), kont, goal.allHeaplets - newGoal.allHeaplets, this))
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

  object PureUnify extends SynthesisRule {
    override def toString: String = "PureUnify"

    def apply(goal: Goal): Seq[RuleResult] = {
      // get post conjuncts with existentials
      val postConjuncts = goal.post.phi.conjuncts.filter(p => p.vars.exists(goal.isExistential) && p.allowUnify).toList
      val preConjuncts = goal.pre.phi.conjuncts.filter(p => p.allowUnify).toList

      for {
        s <- postConjuncts
        t <- preConjuncts
        sigma <- PureUnification.tryUnify(t, s, goal.existentials)
        newGoal = goal.spawnChild(post = goal.post.subst(sigma))
        kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
      } yield RuleResult(List(newGoal), kont, goal.allHeaplets - newGoal.allHeaplets, this)
    }
  }

  /*
    Γ, l ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l * Q}[l/m] ---> S   m is existential
  --------------------------------------------------------------------------------[pick-from-env]
     Γ ; {φ ; x.f -> - * P} ; {ψ ; x.f -> m * Q} ---> *x.f := l ; S
   */
  object PickFromEnvRule extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "WriteFromEnv"

    def apply(goal: Goal): Seq[RuleResult] = {

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
            l <- goal.programVars
            if goal.gamma(l).conformsTo(Some(IntType))
            newPre = Assertion(pre.phi, (goal.pre.sigma - hl) ** PointsTo(x, offset, l))
            subGoal = goal.spawnChild(newPre, post.subst(m, l))
            kont = PrependProducer(Store(x, offset, l)) >> HandleGuard(goal) >> ExtractHelper(goal)
          } yield RuleResult(List(subGoal), kont, goal.allHeaplets - subGoal.allHeaplets, this)
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

  object Pick extends SynthesisRule {
    override def toString: String = "Pick"

    def apply(goal: Goal): Seq[RuleResult] = {
      val constants = List(IntConst(0), SetLiteral(List()), BoolConst(true), BoolConst(false))

      for {
        ex <- least(goal.existentials) // since all existentials must go, no point trying them in different order
        v <- toSorted(goal.allUniversals.intersect(goal.pre.vars ++ goal.post.vars)) ++ constants
        if goal.getType(ex).conformsTo(Some(v.getType(goal.gamma).get))
        sigma = Map(ex -> v)
        if sigma.nonEmpty
        newGoal = goal.spawnChild(post = goal.post.subst(sigma))
        kont = ExistentialProducer(sigma) >> IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
      } yield RuleResult(List(newGoal), kont, goal.allHeaplets - newGoal.allHeaplets, this)
    }
  }
}
