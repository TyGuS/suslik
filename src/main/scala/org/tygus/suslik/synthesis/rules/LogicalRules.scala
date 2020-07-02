package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Ident
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules._

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
  object EmpRule extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "Emp"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      if (pre.sigma.isEmp && post.sigma.isEmp && // heaps are empty
        goal.existentials.isEmpty &&             // no existentials
        SMTSolving.valid(pre.phi ==> post.phi))  // pre implies post
        List(RuleResult(Nil, ConstProducer(Skip), this, goal))      // we are done
      else Nil
    }
  }

  /*
  --------------------------------------- [inconsistency]
  Γ ; {φ ∧ l ≠ l ; P} ; {ψ ; Q} ---> emp

  The other axiom: pre is inconsistent -> emit error
  */
  object Inconsistency extends SynthesisRule with InvertibleRule {
    override def toString: String = "Inconsistency"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre.phi.toExpr

      if (!SMTSolving.sat(pre))
        List(RuleResult(Nil, ConstProducer(Error), this, goal)) // pre inconsistent: return error
      else
        Nil
    }
  }

  /*
   Remove conjuncts from the pure pre if their variables do not occur anywhere else
  */
  object WeakenPre extends SynthesisRule with InvertibleRule {
    override def toString: String = "WeakenPre"

    def apply(goal: Goal): Seq[RuleResult] = {
      val unused = goal.pre.phi.indepedentOf(goal.pre.sigma.vars ++ goal.post.vars)
      if (unused.conjuncts.isEmpty) Nil
      else {
        val newPre = Assertion(goal.pre.phi - unused, goal.pre.sigma)
        val newGoal = goal.spawnChild(pre = newPre)
        val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
        List(RuleResult(List(newGoal), kont, this, goal))
      }
    }
  }


  /*
   Remove an equivalent heaplet from pre and post
   */
  abstract class Frame extends SynthesisRule {
    def heapletFilter(h: Heaplet): Boolean

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && heapletFilter(hPost)

      findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
        case None => Nil
        case Some((hPre, hPost)) => {
          val newPreSigma = pre.sigma - hPre
          val newPostSigma = post.sigma - hPost
          val newPre = Assertion(pre.phi, newPreSigma)
          val newPost = Assertion(post.phi, newPostSigma)
          val newGoal = goal.spawnChild(newPre, newPost)
          val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
          List(RuleResult(List(newGoal), kont, this, goal))
        }
      }
    }
  }

  object FrameUnfolding extends Frame with UnfoldingPhase {
    override def toString: String = "FrameUnfold"
  }

  object FrameUnfoldingFinal extends Frame with UnfoldingPhase with InvertibleRule {
    override def toString: String = "FrameUnfold"
  }

  object FrameBlock extends Frame with BlockPhase with InvertibleRule {
    override def toString: String = "FrameBlock"
  }

  object FrameFlat extends Frame with FlatPhase with InvertibleRule {
    override def toString: String = "FrameFlat"
  }


  /*
  x ≠ nil ∉ φ
  Γ ; {φ ∧ x ≠ nil ; x.f -> l * P} ; {ψ ; Q} ---> S
  -------------------------------------------------- [nil-not-lval]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; Q} ---> S
  */

  object NilNotLval extends SynthesisRule with InvertibleRule {
    override def toString: String = "NilNotLval"

    def apply(goal: Goal): Seq[RuleResult] = {

      // Find pointers in `a` that are not yet known to be non-null
      def findPointers(a: Assertion): Set[Expr] = {
        val p = a.phi
        // All pointers
        val allPointers = (for (PointsTo(l, _, _) <- a.sigma.chunks) yield l).toSet
        allPointers.filter(
          x => p != pFalse && !p.conjuncts.contains(x |/=| NilPtr) && !p.conjuncts.contains(NilPtr |/=| x)
        )
      }

      def addToAssertion(a: Assertion, ptrs: Set[Expr]): Assertion = {
        Assertion(a.phi && PFormula(ptrs.map { x => x |/=| NilPtr }), a.sigma)
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
        val newGoal = goal.spawnChild(newPre, newPost)
        val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
        List(RuleResult(List(newGoal), kont, this, goal))
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
    override def toString: String = "*Partial"

    def extendPure(p: PFormula, s: SFormula, excludeVars: Set[Var]): Option[(PFormula, SFormula)] = {
      val ptrs = (for (PointsTo(x, o, _) <- s.chunks) yield (o, x)).groupBy(_._1).mapValues(_.map(_._2))
      // All pairs of pointers
      val pairs = for (o <- ptrs.keySet; x <- ptrs(o); y <- ptrs(o) if x != y) yield (x, y)
      val newPairs = pairs.filter {
        case (x, y) => excludeVars.intersect(x.vars ++ y.vars).isEmpty &&
          p != pFalse && !p.conjuncts.contains(x |/=| y) && !p.conjuncts.contains(y |/=| x)
      }
      val allNewVars = newPairs.map(_._1).union(newPairs.map(_._2))
      val heaplets = (for (h@PointsTo(x, _, _) <- s.chunks if allNewVars.contains(x)) yield h)
      if (newPairs.isEmpty) None
      else Some((p && PFormula(newPairs.map { case (x, y) => x |/=| y }), mkSFormula(heaplets)))
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val s1 = goal.pre.sigma
      val s2 = goal.post.sigma
      val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)

      (extendPure(goal.pre.phi, s1, Set.empty), extendPure(goal.post.phi, s2, goal.existentials)) match {
//      (extendPure(goal.pre.phi, s1, Set.empty), extendPure(goal.post.phi, s2, Set.empty)) match {
          // TODO: make sure it's complete to include post, otherwise revert to pre only
        case (None, None) => Nil
        case (Some((p1, ss1)), None) =>
          val newGoal = goal.spawnChild(pre = Assertion(p1, s1))
          List(RuleResult(List(newGoal), kont, this, goal))
        case (None, Some((p2, ss2))) =>
          val newGoal = goal.spawnChild(post = Assertion(p2, s2))
          List(RuleResult(List(newGoal), kont, this, goal))
        case (Some((p1, ss1)), Some((p2, ss2))) =>
          val newGoal = goal.spawnChild(pre = Assertion(p1, s1), post = Assertion(p2, s2))
          List(RuleResult(List(newGoal), kont, this, goal))
//        case (None, _) => Nil
//        case (Some(p1), _) =>
//          val newGoal = goal.spawnChild(pre = Assertion(p1, s1))
//          List(Subderivation(List(newGoal), pureKont(toString)))
      }
    }
  }


  /*
  Γ ; {[l/x]φ ; [l/x]P} ; {[l/x]ψ ; [l/x]Q} ---> S
  ------------------------------------------------ [subst-L]
  Γ ; {φ ∧ x = l ; P} ; {ψ ; Q} ---> S
  */
  object SubstLeft extends SynthesisRule with InvertibleRule {
    override def toString: String = "SubstL"

    def apply(goal: Goal): Seq[RuleResult] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma
      val p2 = goal.post.phi
      val s2 = goal.post.sigma
      val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)

      findConjunctAndRest({
        case BinaryExpr(OpEq, v1@Var(_), e2) => !e2.vars.contains(v1)
        case BinaryExpr(OpSetEq, v1@Var(_), e2) => !e2.vars.contains(v1)
        case BinaryExpr(OpBoolEq, v1@Var(_), e2) => !e2.vars.contains(v1)
        case _ => false
      }, p1) match {
        case Some((BinaryExpr(_, x@Var(_), l), rest1)) =>
          val _p1 = rest1.subst(x, l)
          val _s1 = s1.subst(x, l)
          val _p2 = p2.subst(x, l)
          val _s2 = s2.subst(x, l)
          val newGoal = goal.spawnChild(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2))
            List(RuleResult(List(newGoal), kont, this, goal))
        case _ => Nil
      }
    }
  }

  // This rule has to come after inconsistency
  object SubstLeftVar extends SynthesisRule with InvertibleRule {
    override def toString: String = "SubstLVar"

    def snapshot(g: Goal): PFormula =
      if (g.preNormalized) {
        g.pre.phi
      } else g.parent match {
        case None => pTrue
        case Some(p) => snapshot(p)
      }

    def apply(goal: Goal): Seq[RuleResult] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma
      val p2 = goal.post.phi
      val s2 = goal.post.sigma
      val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)

      val normalizedPre = snapshot(goal)
      val diff = p1 - normalizedPre
      val diffDependent = p1 - p1.indepedentOf(diff.vars)
      val varCandidates =
          (goal.programVars ++ goal.universalGhosts.toList.sortBy(_.name)).filter(x => diffDependent.vars.contains(x))

      val subs: List[(Var, Var)] = for {
        v1 <- varCandidates.reverse // prefer replacing later vars
        v2 <- varCandidates.take(varCandidates.indexOf(v1)).find(v =>
          goal.getType(v1) == goal.getType(v) &&
            SMTSolving.valid(p1 ==> v1.eq(v, goal.getType(v)))
        ) // prefer replacing with earlier variables
      } yield v1 -> v2
      
      subs match {
        case Nil => Nil
        case _ =>
          val sub = subs.toMap
          val _p1 = p1.subst(sub)
          val _s1 = s1.subst(sub)
          val _p2 = p2.subst(sub)
          val _s2 = s2.subst(sub)
          val newGoal = goal.spawnChild(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2),
            preNormalized = true)
          List(RuleResult(List(newGoal), kont, this, goal))
      }
    }
  }

  // If an exsitential has a unique solution that is a variable, substitute
  object SubstRightVar extends SynthesisRule with InvertibleRule {
    override def toString: String = "SubstRVar"

    def snapshot(g: Goal): PFormula =
      if (g.postNormalized) {
        g.pre.phi && g.post.phi
      } else g.parent match {
        case None => pTrue
        case Some(p) => snapshot(p)
      }

    def apply(goal: Goal): Seq[RuleResult] = {
      val p1 = goal.pre.phi
      val p2 = goal.post.phi
      val s2 = goal.post.sigma
      val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)

      val normalized = snapshot(goal)
      val prePost = p1 && p2
      val diff = prePost - normalized
      val lhsCandidates = (goal.existentials -- diff.vars).toList
      val rhsCandidates = (goal.programVars ++ goal.universalGhosts.toList.sortBy(_.name)).filter(x => diff.vars.contains(x))


      val subs: List[(Var, Var)] = for {
        v1 <- lhsCandidates
        v2 <- rhsCandidates
        if goal.getType(v1) == goal.getType(v2)
        if SMTSolving.valid(prePost.toExpr ==> v1.eq(v2, goal.getType(v1)))
      } yield (v1, v2)

      subs match {
        case Nil => Nil
        case _ :: _ =>
          val sub = subs.toMap
          val _p2 = p2.subst(sub)
          val _s2 = s2.subst(sub)
          val newGoal = goal.spawnChild(post = Assertion(_p2, _s2), postNormalized = true)
          List(RuleResult(List(newGoal), kont, this, goal))
      }
    }
  }

}
