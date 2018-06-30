package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Statements.Magic
import org.tygus.synsl.logic.Specifications.Goal
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.logic.{PureLogicUtils, SepLogicUtils}
import org.tygus.synsl.synthesis._
import org.tygus.synsl.synthesis.rules.OperationalRules.{AllocRule, FreeRule}

/**
  * Rules for short-circuiting failure;
  * do not affect completeness, they are simply an optimization.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object FailRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-fail"

  // Short-circuits failure if pure post is inconsistent with the pre
  object PostInconsistent extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: post-inconsistent]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      if (!SMTSolving.sat(andClean(pre, post)))
        List(Subderivation(Nil, _ => Magic)) // post inconsistent: only magic can save us
      else
        Nil
    }
  }


  // Short-circuits failure if universal part of post is too strong
  object PostInvalid extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Norm: post-invalid]"

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
  // This rule is only applicable if alloc and free aren't
  object HeapUnreachable extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Norm: heap-unreachable]"

    def apply(goal: Goal): Seq[Subderivation] = {
      (AllocRule.findTargetHeaplets(goal), FreeRule.findTargetHeaplets(goal)) match {
        case (None, None) =>
          if (goal.pre.sigma.chunks.length == goal.post.sigma.chunks.length)
            Nil
          else
            List(Subderivation(Nil, _ => Magic)) // spatial parts do not match: only magic can save us
        case _ => Nil // does not apply if we could still alloc or free
      }

    }
  }
}
