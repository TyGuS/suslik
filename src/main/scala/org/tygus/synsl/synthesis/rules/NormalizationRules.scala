package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.logic.Specifications._
import org.tygus.synsl.synthesis._

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

  object NilNotLval extends SynthesisRule with InvertibleRule {
    override def toString: String = "[Norm: nil-not-lval]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {

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
        List(Subderivation(List((newGoal, env)), pureKont(toString)))
      }
    }
  }

  /*
  x ≠ y ∉ φ
  Γ ; {φ ∧ x ≠ y ; x.f -> l * y.f -> l' * P} ; {ψ ; Q} ---> S
  ------------------------------------------------------------ [*-partial]
  Γ ; {φ ; x.f -> l * y.f -> l' * P} ; {ψ ; Q} ---> S
   */
  object StarPartial extends SynthesisRule with InvertibleRule {
    override def toString: String = "[Norm: *-partial]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma

      val cs = conjuncts(p1)
      val ptrs = (for (PointsTo(x, _, _) <- s1.chunks) yield x).toSet
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
      if (newPairs.isEmpty) return Nil

      // The implementation immediately adds _all_ inequalities
      val _p1 = mkConjunction(cs ++ newPairs.map { case (x, y) => x |/=| y })
      val newGoal = goal.copy(Assertion(_p1, s1))
      List(Subderivation(List((newGoal, env)), pureKont(toString)))
    }
  }


  /*
  Γ ; {[l/x]φ ; [l/x]P} ; {[l/x]ψ ; [l/x]Q} ---> S
  ------------------------------------------------ [subst-L]
  Γ ; {φ ∧ x = l ; P} ; {ψ ; Q} ---> S
  */
  object SubstLeft extends SynthesisRule with InvertibleRule {
    override def toString: String = "[Norm: subst-L]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      findConjunctAndRest({
        case BinaryExpr(OpEq, v1@Var(_), v2) => v1 != v2
        case _ => false
      }, simplify(p1)) match {
        case Some((BinaryExpr(OpEq, x@Var(_), l), rest1)) =>
          val _p1 = mkConjunction(rest1).subst(x, l)
          val _s1 = s1.subst(x, l)
          val _p2 = p2.subst(x, l)
          val _s2 = s2.subst(x, l)
          val newGoal = goal.copy(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2))
          List(Subderivation(List((newGoal, env)), pureKont(toString)))
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
  object SubstRight extends SynthesisRule with InvertibleRule {
    override def toString: String = "[Norm: subst-R]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val p2 = goal.post.phi
      val s2 = goal.post.sigma


      def isExsistVar(e: Expr) = e.isInstanceOf[Var] && goal.isExistential(e.asInstanceOf[Var])

      findConjunctAndRest({
        case BinaryExpr(OpEq, l, r) => isExsistVar(l) || isExsistVar(r)
        case _ => false
      }, simplify(p2)) match {
        case Some((BinaryExpr(OpEq, l, r), rest2)) =>
          val (x, e) = if (isExsistVar(l)) {
            (l.asInstanceOf[Var], r)
          } else {
            (r.asInstanceOf[Var], l)
          }
          val _p2 = mkConjunction(rest2).subst(x, e)
          val _s2 = s2.subst(x, e)
          val newGoal = goal.copy(post = Assertion(_p2, _s2))
          List(Subderivation(List((newGoal, env)), pureKont(toString)))
        case _ => Nil
      }
    }
  }


  /*
  --------------------------------------- [inconsistency]
  Γ ; {φ ∧ l ≠ l ; P} ; {ψ ; Q} ---> emp
  */
  object Inconsistency extends SynthesisRule with InvertibleRule {
    override def toString: String = "[Norm: inconsistency]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
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

  // TODO: remove me once full SMT support in Emp is provided
  /*
  Γ ; {φ ∧ φ' ; P} ; {ψ ; Q} ---> S
  --------------------------------------- [Hypothesis]
  Γ ; {φ ∧ φ' ; P} ; {ψ ∧ φ' ; Q} ---> S
  */
  object Hypothesis extends SynthesisRule with InvertibleRule {
    override def toString: String = "[Norm: hypothesis]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val cs1 = conjuncts(goal.pre.phi)
      val cs2 = conjuncts(goal.post.phi)
      findCommon((p: PFormula) => true, cs1, cs2) match {
        case Some((p, ps1, ps2)) =>
          val newPost = Assertion(mkConjunction(ps2), goal.post.sigma)
          val newGoal = goal.copy(post = newPost)
          List(Subderivation(List((newGoal, env)), pureKont(toString)))
        case None => Nil
      }
    }
  }

}
