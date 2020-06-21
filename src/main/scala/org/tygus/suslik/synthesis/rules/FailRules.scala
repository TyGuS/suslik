package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.IntType
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic._
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
        List(RuleResult(List(goal.unsolvableChild), IdProducer, goal.allHeaplets, this))
      else
        Nil
    }
  }

  // Short-circuits failure if universal part of post is too strong
  object PostInvalid extends SynthesisRule with InvertibleRule {
    override def toString: String = "PostInvalid"

    def apply(goal: Goal): Seq[RuleResult] = {
      // If precondition does not contain predicates, we can't get get new facts from anywhere
      if (!SMTSolving.valid(goal.pre.phi ==> goal.universalPost))
        // universal post not implies by pre
        List(RuleResult(List(goal.unsolvableChild), IdProducer, goal.allHeaplets, this))
      else
        Nil
    }
  }

  object AbduceBranch extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString: String = "AbduceBranch"

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
        subset <- atoms.toSet.subsets.toSeq.sortBy(_.size)
        if subset.nonEmpty
      } yield PFormula(subset).toExpr
    }

    /**
      * Find the earliest ancestor of goal
      * that is still valid and has all variables from vars
      */
    def findBranchPoint(vars: Set[Var], goal: Goal): Option[Goal] = {
      def valid(g: Goal) = SMTSolving.valid(g.pre.phi ==> g.universalPost)

      goal.parent match {
        case None => Some(goal).filter(valid) // goal is root: return itself if valid
        case Some(pGoal) =>
          if (vars.subsetOf(pGoal.programVars.toSet)) {
            // Parent goal has all variables from vars: recurse
            findBranchPoint(vars, pGoal)
          } else Some(goal).filter(valid) // one of vars undefined in the goal: return itself if valid
      }
    }

    def guardedCandidates(goal: Goal): Seq[RuleResult] =
      for {
        cond <- condCandidates(goal)
        pre = goal.pre.phi
        if SMTSolving.valid((pre && cond) ==> goal.universalPost)
        if SMTSolving.sat((pre && cond).toExpr)
        bGoal <- findBranchPoint(cond.vars, goal)
        thenGoal = goal.spawnChild(goal.pre.copy(phi = goal.pre.phi && cond), childId = Some(0))
        elseGoal = bGoal.spawnChild(
          pre = bGoal.pre.copy(phi = bGoal.pre.phi && cond.not),
          childId = Some(1))
      } yield RuleResult(List(thenGoal, elseGoal),
        GuardedProducer(cond, bGoal),
        goal.allHeaplets,
        this)

    def apply(goal: Goal): Seq[RuleResult] = {
      if (SMTSolving.valid(goal.pre.phi ==> goal.universalPost))
        Nil // valid so far, nothing to say
      else {
        val guarded = guardedCandidates(goal)
        if (guarded.isEmpty)
          // Abduction failed
          List(RuleResult(List(goal.unsolvableChild), IdProducer, goal.allHeaplets, this)) // pre doesn't imply post: goal is unsolvable
        else guarded.take(1) // TODO: try several incomparable conditions, but filter out subsumed ones?
      }
    }
  }


  // Short-circuits failure if spatial post doesn't match pre
  // This rule is only applicable when only points-to heaplets are left
  object HeapUnreachable extends SynthesisRule with InvertibleRule {
    override def toString: String = "HeapUnreachable"

    def apply(goal: Goal): Seq[RuleResult] = {
      assert(!(goal.hasPredicates() || goal.hasBlocks))
      if ((goal.pre.sigma.profile == goal.post.sigma.profile) && // profiles must match
        goal.post.sigma.chunks.forall { case pts@PointsTo(v@Var(_), _, _) => goal.isExistential(v) || // each post heaplet is either existential pointer
          findHeaplet(sameLhs(pts), goal.pre.sigma).isDefined
        }) // or has a heaplet in pre with the same LHS
        Nil
      else
        List(RuleResult(List(goal.unsolvableChild), IdProducer, goal.allHeaplets, this)) // spatial parts do not match: only magic can save us
    }
  }

}
