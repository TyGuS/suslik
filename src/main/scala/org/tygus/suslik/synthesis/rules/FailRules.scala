package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.{Expr, PFormula}
import org.tygus.suslik.language.{Ident, IntType}
import org.tygus.suslik.language.Statements.{Guarded, Magic}
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.{PureLogicUtils, SepLogicUtils}
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.synthesis.rules.OperationalRules.{AllocRule, FreeRule}

/**
  * Rules for short-circuiting failure;
  * do not affect completeness, they are simply an optimization.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object FailRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-fail"

  // Noop rule: never applies (used to replace disabled rules)
  object Noop extends SynthesisRule with AnyPhase {
    override def toString: String = "[Fail: noop]"

    def apply(goal: Goal): Seq[Subderivation] = Nil
  }

  // Short-circuits failure if pure post is inconsistent with the pre
  object PostInconsistent extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Fail: post-inconsistent]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      if (!SMTSolving.sat(pre && post))
        // post inconsistent with pre
        List(Subderivation(List(goal.unsolvableChild), idProducer("post-inconsistent")))
      else
        Nil
    }
  }


  // Short-circuits failure if universal part of post is too strong
  object PostInvalid extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Fail: post-invalid]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      // If precondition does not contain predicates, we can't get get new facts from anywhere
      val universalPost = mkConjunction(post.conjuncts.filterNot(p => p.vars.exists(goal.isExistential)))
      if (!SMTSolving.valid(pre ==> universalPost))
        // universal post not implies by pre
        List(Subderivation(List(goal.unsolvableChild), idProducer("post-invalid")))
      else
        Nil
    }
  }

  object AbduceBranch extends SynthesisRule with FlatPhase {

    override def toString: Ident = "[Fail: abduce-branch]"

    def atomCandidates(goal: Goal): Seq[Expr] =
      for {
        lhs <- goal.programVars
        rhs <- goal.programVars
        if lhs != rhs
        if goal.getType(lhs) == IntType && goal.getType(rhs) == IntType
      } yield lhs |<=| rhs

    def condCandidates(goal: Goal): Seq[Expr] = {
      val atoms = atomCandidates(goal)
      // Toggle this to enable abduction of conjunctions
      // (without branch pruning, produces too many branches)
//      atoms
      for {
        subset <- atoms.toSet.subsets.toSeq
        if subset.nonEmpty
      } yield simplify(mkConjunction(subset.toList))
    }

    def guardedCandidates(goal: Goal, pre: PFormula, post: PFormula): Seq[Subderivation] =
      for {
        cond <- condCandidates(goal)
        if SMTSolving.valid((pre && cond) ==> post)
        if SMTSolving.sat(pre && cond)
        newPre = goal.pre.copy(phi = goal.pre.phi && cond)
        newGoal = goal.spawnChild(newPre)
      } yield Subderivation(List(newGoal),
        StmtProducer(1, liftToSolutions(stmts => Guarded(cond, stmts.head)), "abduce-branch"))

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      val universalPost = mkConjunction(post.conjuncts.filterNot(p => p.vars.exists(goal.isExistential)))
      if (SMTSolving.valid(pre ==> universalPost))
        Nil // valid so far, nothing to say
      else {
        val guarded = guardedCandidates(goal, pre, universalPost)
        if (guarded.isEmpty)
          if (goal.env.config.fail)
            List(Subderivation(List(goal.unsolvableChild), idProducer("abduce-branch-fail"))) // pre doesn't imply post: only magic can save us
          else
            Nil // would like to return Magic, but fail optimization is disabled
        else guarded
      }
    }
  }


  // Short-circuits failure if spatial post doesn't match pre
  // This rule is only applicable if alloc and free aren't
  object HeapUnreachable extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Fail: heap-unreachable]"

    def apply(goal: Goal): Seq[Subderivation] = {
      (AllocRule.findTargetHeaplets(goal), FreeRule.findTargetHeaplets(goal)) match {
        case (None, None) =>
          if (goal.pre.sigma.chunks.length == goal.post.sigma.chunks.length)
            Nil
          else
            List(Subderivation(List(goal.unsolvableChild), idProducer("heap-unreachable"))) // spatial parts do not match: only magic can save us
        case _ => Nil // does not apply if we could still alloc or free
      }

    }
  }
}
