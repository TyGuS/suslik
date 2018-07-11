package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{Ident, IntType}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis._

/**
  * Logical rules simplify specs and terminate the derivation;
  * they do not eliminate existentials.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object LogicalRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-logical"

  /*

    -------------------------------- [emp]
    Γ ; {φ ; emp} ; {emp} ---> skip

    Axiom: heaps are empty and pure spec is valid -> emit skip

  */
  object EmpRule extends SynthesisRule with FlatPhase with InvertibleRule {

    override def toString: Ident = "[Sub: emp]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post

      if (pre.sigma.isEmp && post.sigma.isEmp && // heaps are empty
        goal.existentials.isEmpty &&             // no existentials
        SMTSolving.valid(pre.phi ==> post.phi))  // pre implies post
        List(Subderivation(Nil, _ => Skip))      // we are done
      else Nil
    }
  }

  /*
  --------------------------------------- [inconsistency]
  Γ ; {φ ∧ l ≠ l ; P} ; {ψ ; Q} ---> emp

  The other axiom: pre is inconsistent -> emit error
  */
  object Inconsistency extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: inconsistency]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      if (!SMTSolving.sat(pre))
        List(Subderivation(Nil, _ => Error)) // pre inconsistent: return error
      else
        Nil
    }
  }


  /*
   Remove an equivalent heaplet from pre and post
   */
  abstract class Frame extends SynthesisRule {
    def heapletFilter(h: Heaplet): Boolean

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post
      val deriv = goal.deriv

      def isSuitable(hPost: Heaplet): Boolean = !hPost.vars.exists(goal.isExistential) && heapletFilter(hPost)
      def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && isSuitable(hPost)

      findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
        case None => Nil
        case Some((hPre, hPost)) => {
          val newPreSigma = pre.sigma - hPre
          val newPostSigma = post.sigma - hPost
          val newPre = Assertion(pre.phi, newPreSigma)
          val newPost = Assertion(post.phi, newPostSigma)
          val preFootprint = Set(deriv.preIndex.lastIndexOf(hPre))
          val postFootprint = Set(deriv.postIndex.lastIndexOf(hPost))
          val ruleApp = saveApplication((preFootprint, postFootprint), deriv)
          val newGoal = goal.copy(newPre, newPost, newRuleApp = Some(ruleApp))
          List(Subderivation(List(newGoal), pureKont(toString)))
        }
      }
    }
  }

  object FrameUnfolding extends Frame with UnfoldingPhase {
    override def toString: String = "[Sub: frame-unfold]"
  }

  object FrameFlat extends Frame with FlatPhase with InvertibleRule {
    override def toString: String = "[Sub: frame-flat]"
  }


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

    def extendPure(p: PFormula, s: SFormula, excludeVars: Set[Var]): Option[PFormula] = {
      val cs = conjuncts(p)
      val ptrs = (for (PointsTo(x, _, _) <- s.chunks) yield x).toSet
      // All pairs of pointers
      val pairs = for (x <- ptrs; y <- ptrs if x != y) yield (x, y)
      val newPairs = pairs.filter {
        case (x, y) => excludeVars.intersect(x.vars ++ y.vars).isEmpty &&
          !cs.contains(x |/=| y) && !cs.contains(y |/=| x)
      }
      if (newPairs.isEmpty) None
      else Some(mkConjunction(cs ++ newPairs.map { case (x, y) => x |/=| y }))
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      val s1 = goal.pre.sigma
      val s2 = goal.post.sigma

      (extendPure(goal.pre.phi, s1, Set.empty), extendPure(goal.post.phi, s2, goal.existentials)) match {
          // TODO: make sure it's complete to include post, otherwise revert to pre only
        case (None, None) => Nil
        case (Some(p1), None) =>
          val newGoal = goal.copy(pre = Assertion(p1, s1))
          List(Subderivation(List(newGoal), pureKont(toString)))
        case (None, Some(p2)) =>
          val newGoal = goal.copy(post = Assertion(p2, s2))
          List(Subderivation(List(newGoal), pureKont(toString)))
        case (Some(p1), Some(p2)) =>
          val newGoal = goal.copy(pre = Assertion(p1, s1), post = Assertion(p2, s2))
          List(Subderivation(List(newGoal), pureKont(toString)))
//        case (None, _) => Nil
//        case (Some(p1), _) =>
//          val newGoal = goal.copy(pre = Assertion(p1, s1))
//          List(Subderivation(List(newGoal), pureKont(toString)))
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
      }, p1) match {
        case Some((BinaryExpr(_, x@Var(_), l), rest1)) =>
          val _p1 = mkConjunction(rest1).subst(x, l)
          val _s1 = s1.subst(x, l)
          val _p2 = p2.subst(x, l)
          val _s2 = s2.subst(x, l)
          val newGoal = goal.copy(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2))
            List(Subderivation(List(newGoal), pureKont(toString)))
        case _ => Nil
      }
    }
  }

  // This rule has to come after inconsistency
  object SubstLeftVar extends SynthesisRule with UnfoldingPhase with InvertibleRule {
    override def toString: String = "[Norm: subst-L-var]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      val varCandidates = goal.programVars ++ goal.universalGhosts.toList.sortBy(_.name)

      lazy val subs: List[Subst] = for {
        v1 <- varCandidates
        v2 <- varCandidates.drop(varCandidates.indexOf(v1) + 1)
        if goal.getType(v1) == goal.getType(v2)
        if SMTSolving.valid(p1 ==> v1.eq(v2, goal.getType(v1)))
      } yield Map(v2 -> v1)

      subs match {
        case Nil => Nil
        case sub :: _ =>
          val _p1 = p1.subst(sub)
          val _s1 = s1.subst(sub)
          val _p2 = p2.subst(sub)
          val _s2 = s2.subst(sub)
          val newGoal = goal.copy(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2))
          List(Subderivation(List(newGoal), pureKont(toString)))
      }
    }
  }
}
