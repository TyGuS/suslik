package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.IntType
import org.tygus.suslik.language.Statements.Guarded
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.FailRules.CheckPost
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Rules for branch abduction
  *
  * @author Nadia Polikarpova
  */

object BranchRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-branch"

  /**
    * Generates speculative conditionals, using an unknown predicate as the condition.
    * If then-branch generates a guarded statement, its guard replaces the unknown;
    * otherwise the unknown is instantiated to `true`.
    * The else branch is generated under the negation of the unknown,
    * and hence is vacuous unless the then-branch is guarded.
    */
  object Branch extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString: String = "Branch"

    val unknownCondPrefix = "C-"
    val varSeparator = "-"

    def isUnknownCond(v: Var) = v.name.startsWith(unknownCondPrefix)

    def unknownCond(goal: Goal): Var = {
      val suffix = goal.programVars.map(_.name).mkString(varSeparator)
      Var(unknownCondPrefix ++ suffix)
    }

    def minimalUnknown(phi: PFormula, mustHaveVars: Set[Var]): Var = {
      val allCondVars = phi.vars.filter(isUnknownCond)
      val m = allCondVars.map(v => (v, v.name.stripPrefix(unknownCondPrefix).split(varSeparator).toSet.map(Var))).toList.sortBy(_._2.size)
      m.find({ case (_, vs) => mustHaveVars.subsetOf(vs)}).get._1
    }

    def substUnknown(phi: PFormula, cond: Expr, mustHaveVars: Set[Var]): PFormula = {
      val theVar = minimalUnknown(phi, mustHaveVars)
      phi.subst(theVar, cond)
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val unknown = unknownCond(goal)
      val thenGoal = goal.spawnChild(pre = Assertion(pre.phi && unknown, pre.sigma), childId = Some(0))
      //      val elseGoal = goal.spawnChild(pre = Assertion(pre.phi && unknown.not, pre.sigma), childId = Some(1))
      val elseGoal = goal.spawnChild(pre = Assertion(pFalse, pre.sigma), childId = Some(1))

      val elseGoalUpdater: GoalUpdater = sols => g => {
        assert(sols.size == 1)
        //      val knownCond = sols.head._1 match {
        //        case Guarded(cond, _) if minimalUnknown(g.pre.phi, cond.vars) == unknownCond(g) => cond
        //        case _ => BoolConst(true)
        //      }
        //      g.copy(pre = g.pre.copy(phi = substUnknown(g.pre.phi, knownCond, g.programVars.toSet)))
        sols.head._1 match {
          case Guarded(cond, _) if minimalUnknown(thenGoal.pre.phi, cond.vars) == unknown =>
            g.copy(pre = g.pre.copy(phi = goal.pre.phi && cond.not))
          case _ => g
        }
      }

      List(RuleResult(List(thenGoal, elseGoal), GuardedBranchProducer(thenGoal), this, goal).copy(updates =
        List(RuleResult.noUpdate, elseGoalUpdater)))
    }
  }

  /**
    * If post is invalid, finds a weakest predicate over program variables that makes it valid.
    * If abduction succeeds (i.e. minimal predicate is not `false`), generates the rest of the program and wraps it in a guarded statement.
    * If abduction fails (minimal predicate is `false`), acts as the failure rule CheckPost.
    */
  object AbduceBranch extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString: String = "AbduceBranch"

    def atomCandidates(goal: Goal): Seq[Expr] =
      for {
        lhs <- goal.programVars.filter(goal.post.phi.vars.contains)
        rhs <- goal.programVars.filter(goal.post.phi.vars.contains)
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
        if subset.nonEmpty && subset.size <= goal.env.config.maxGuardConjuncts
      } yield PFormula(subset).toExpr
    }

    def guardedCandidates(goal: Goal): Seq[RuleResult] =
      for {
        cond <- condCandidates(goal)
        pre = goal.pre.phi
        if SMTSolving.valid((pre && cond) ==> goal.universalPost)
        if SMTSolving.sat((pre && cond).toExpr)
        thenGoal = goal.spawnChild(goal.pre.copy(phi = Branch.substUnknown(goal.pre.phi, cond, cond.vars)))
      } yield {
        RuleResult(List(thenGoal), GuardedProducer(cond), this, thenGoal)
      }

    def apply(goal: Goal): Seq[RuleResult] = {
      val (uniPost, exPost) = goal.splitPost
      if (SMTSolving.valid(goal.pre.phi ==> uniPost))
        CheckPost.filterOutValidPost(goal, exPost, uniPost)
      else {
        val guarded = guardedCandidates(goal)
        if (guarded.isEmpty)
        // Abduction failed
          List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal)) // pre doesn't imply post: goal is unsolvable
        else guarded.take(1) // TODO: try several incomparable conditions, but filter out subsumed ones?
      }
    }
  }

}

