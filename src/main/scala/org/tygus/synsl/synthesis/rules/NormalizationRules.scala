package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.logic.Specifications._
import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules.OperationalRules.AllocRule

import scala.collection.Set

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

object NormalizationRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-normalization"

  /*
  x ≠ nil ∉ φ
  Γ ; {φ ∧ x ≠ nil ; x.f -> l * P} ; {ψ ; Q} ---> S
  -------------------------------------------------- [nil-not-lval]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; Q} ---> S
  */

  object NilNotLval extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: nil-not-lval]"

    def apply(goal: Goal): Seq[Subderivation] = {

      // Find pointers in `a` that are not yet known to be non-null
      def findPointers(a: Assertion): Set[Expr] = {
        val cs = conjuncts(a.phi)
        // All pointers
        val allPointers = (for (PointsTo(l, _, _) <- a.sigma.chunks) yield l).toSet
        allPointers.filter(
          x => !cs.contains(x |/=| NilPtr) && !cs.contains(NilPtr |/=| x)
        )
      }


      def addToAssertion(a: Assertion, ptrs: Set[Expr]): Assertion = {
        val cs = conjuncts(a.phi)
        val newPhi = mkConjunction(cs ++ ptrs.map { x => x |/=| NilPtr })
        Assertion(newPhi, a.sigma)
      }

      val pre = goal.pre
      val post = goal.post

      val prePointers = findPointers(pre)
      val postPointers = findPointers(post).filter(_.vars.forall(v => goal.isExistential(v)))

      if (prePointers.isEmpty && postPointers.isEmpty)
        Nil // no pointers to insert
      else {
        val newPre = addToAssertion(pre, prePointers)
        val newPost = addToAssertion(post, postPointers)
        val newGoal = goal.copy(newPre, newPost)
        List(Subderivation(List(newGoal), pureKont(toString)))
      }
    }
  }

  /*
  x ≠ y ∉ φ
  Γ ; {φ ∧ x ≠ y ; x.f -> l * y.f -> l' * P} ; {ψ ; Q} ---> S
  ------------------------------------------------------------ [*-partial]
  Γ ; {φ ; x.f -> l * y.f -> l' * P} ; {ψ ; Q} ---> S
   */
  object StarPartial extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: *-partial]"

    def extendPure(p: PFormula, s: SFormula): Option[PFormula] = {
      val cs = conjuncts(p)
      val ptrs = (for (PointsTo(x, _, _) <- s.chunks) yield x).toSet
      // All pairs of pointers
      val pairs = (for (x <- ptrs; y <- ptrs if x != y) yield Set(x, y)).
        map { s =>
          val elems = s.toList
          ruleAssert(elems.size == 2, "Wrong number of elements in a pair")
          (elems.head, elems.tail.head)
        }.toList
      val newPairs = pairs.filter {
        case (x, y) => !cs.contains(x |/=| y) && !cs.contains(y |/=| x)
      }
      if (newPairs.isEmpty) None
      else Some(mkConjunction(cs ++ newPairs.map { case (x, y) => x |/=| y }))
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      val s1 = goal.pre.sigma
      val s2 = goal.post.sigma

      (extendPure(goal.pre.phi, s1), extendPure(goal.post.phi, s2)) match {
          // TODO: this is not complete, but probably okay if we exclude existentials?
//        case (None, None) => Nil
//        case (Some(p1), None) =>
//          val newGoal = goal.copy(pre = Assertion(p1, s1))
//          List(Subderivation(List(newGoal), pureKont(toString)))
//        case (None, Some(p2)) =>
//          val newGoal = goal.copy(post = Assertion(p2, s2))
//          List(Subderivation(List(newGoal), pureKont(toString)))
//        case (Some(p1), Some(p2)) =>
//          val newGoal = goal.copy(pre = Assertion(p1, s1), post = Assertion(p2, s2))
//          List(Subderivation(List(newGoal), pureKont(toString)))
        case (None, _) => Nil
        case (Some(p1), _) =>
          val newGoal = goal.copy(pre = Assertion(p1, s1))
          List(Subderivation(List(newGoal), pureKont(toString)))
      }
    }
  }


  /*
  Γ ; {[l/x]φ ; [l/x]P} ; {[l/x]ψ ; [l/x]Q} ---> S
  ------------------------------------------------ [subst-L]
  Γ ; {φ ∧ x = l ; P} ; {ψ ; Q} ---> S
  */
  object SubstLeft extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Norm: subst-L]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      findConjunctAndRest({
        case BinaryExpr(OpEq, v1@Var(_), v2) => v1 != v2
        // This messes with hypothesis unify:
//        case BinaryExpr(OpSetEq, v1@Var(_), v2) => v1 != v2
        case _ => false
      }, simplify(p1)) match {
        case Some((BinaryExpr(_, x@Var(_), l), rest1)) =>
          val _p1 = simplify(mkConjunction(rest1).subst(x, l))
          val _s1 = s1.subst(x, l)
          val _p2 = simplify(p2.subst(x, l))
          val _s2 = s2.subst(x, l)
          val newGoal = goal.copy(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2))
            List(Subderivation(List(newGoal), pureKont(toString)))
        case _ => Nil
      }
    }
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
  --------------------------------------- [inconsistency]
  Γ ; {φ ∧ l ≠ l ; P} ; {ψ ; Q} ---> emp
  */
  object Inconsistency extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: inconsistency]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      if (!SMTSolving.sat(pre))
        List(Subderivation(Nil, _ => Error)) // pre inconsistent: return error
      else if (!SMTSolving.sat(andClean(pre, post)))
        List(Subderivation(Nil, _ => Magic)) // post inconsistent: only magic can save us
      else
        Nil
    }
  }

  // Short-circuits failure if universal part of post is too strong
  object PureUnreachable extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Norm: pure-unreach]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      // If precondition does not contain predicates, we can't get get new facts from anywhere
      // TODO: incompatible with abduction
      val universalPost = mkConjunction(conjuncts(post).filterNot(p => p.vars.exists(goal.isExistential)))

      if (!SMTSolving.valid(pre ==> universalPost))
        List(Subderivation(Nil, _ => Magic)) // universal post not implies by pre: only magic can save us
      else
        Nil
    }
  }

  // Short-circuits failure if spatial post doesn't match pre
  // Important: this rule should only fire after alloc and free
  object HeapUnreachable extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Norm: heap-unreach]"

    def apply(goal: Goal): Seq[Subderivation] = {
      AllocRule.findBlockAndChunks(goal) match {
        case None =>
          if (goal.pre.sigma.chunks.length == goal.post.sigma.chunks.length)
            Nil
          else
            List(Subderivation(Nil, _ => Magic)) // spatial parts do not match: only magic can save us
        case Some(_) => Nil // does not apply if there are existential chunks left
      }

    }
  }


  // TODO: remove me once full SMT support in Emp is provided
  /*
  Γ ; {φ ∧ φ' ; P} ; {ψ ; Q} ---> S
  --------------------------------------- [Hypothesis]
  Γ ; {φ ∧ φ' ; P} ; {ψ ∧ φ' ; Q} ---> S
  */
  object Hypothesis extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: hypothesis]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val cs1 = conjuncts(goal.pre.phi)
      val cs2 = conjuncts(goal.post.phi)
      findCommon((p: PFormula) => true, cs1, cs2) match {
        case Some((p, ps1, ps2)) =>
          val newPost = Assertion(mkConjunction(ps2), goal.post.sigma)
          val newGoal = goal.copy(post = newPost)
          List(Subderivation(List(newGoal), pureKont(toString)))
        case None => Nil
      }
    }
  }

}
