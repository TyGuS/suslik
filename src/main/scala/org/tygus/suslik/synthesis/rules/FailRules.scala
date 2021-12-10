package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Rules for short-circuiting failure;
  * do not affect completeness, they are simply an optimization.
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

object FailRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-fail"

  // Short-circuits failure if pure post is inconsistent with the pre
  object PostInconsistent extends SynthesisRule with InvertibleRule {
    override def toString: String = "PostInconsistent"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      if (!SMTSolving.sat((pre && post).toExpr))
      // post inconsistent with pre
        List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal))
      else
        Nil
    }
  }

  // Short-circuits failure if universal part of post is too strong
  object CheckPost extends SynthesisRule with InvertibleRule {
    override def toString: String = "CheckPost"

    def filterOutValidPost(goal: Goal, exPost: PFormula, uniPost: PFormula): Seq[RuleResult] = {
      val validExConjuncts = exPost.conjuncts.filter(c => SMTSolving.valid(goal.pre.phi ==> c))
      if (validExConjuncts.isEmpty && uniPost.conjuncts.isEmpty) Nil
      else {
        val newPost = Assertion(exPost - PFormula(validExConjuncts), goal.post.sigma)
        val newGoal = goal.spawnChild(post = newPost)
        List(RuleResult(List(newGoal), PureEntailmentProducer(goal.pre.phi, uniPost, goal.gamma) >> IdProducer, this, goal))
      }
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val (uniPost, exPost) = goal.splitPost
      // If precondition does not contain predicates, we can't get new facts from anywhere
      if (!SMTSolving.valid(goal.pre.phi ==> uniPost))
      // universal post not implied by pre
        List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal))
      else filterOutValidPost(goal, exPost, uniPost)
    }
  }

  // Short-circuits failure if spatial post doesn't match pre
  // This rule is only applicable when only points-to heaplets are left
  object HeapUnreachable extends SynthesisRule with InvertibleRule {
    override def toString: String = "HeapUnreachable"

    def apply(goal: Goal): Seq[RuleResult] = {
      assert(!(goal.hasPredicates() || goal.hasBlocks))
      if ((goal.pre.sigma.profile == goal.post.sigma.profile) && // profiles must match
        goal.post.sigma.chunks.forall {
          case pts@PointsTo(v@Var(_), _, _, _) => goal.isExistential(v) || // each post heaplet is either existential pointer
            findHeaplet(sameLhs(pts), goal.pre.sigma).isDefined
          case _ => false
        }) // or has a heaplet in pre with the same LHS
        Nil
      else
        List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal)) // spatial parts do not match: only magic can save us
    }
  }

}
