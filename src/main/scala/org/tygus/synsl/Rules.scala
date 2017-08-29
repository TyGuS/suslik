package org.tygus.synsl

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.language.Statements
import org.tygus.synsl.logic.Specifications

/**
  * An implementation of a rule for synthesis
  *
  * @author Ilya Sergey
  */

trait Rules {

  import Specifications._
  import Statements._


  type Pre = Assertion
  type Post = Assertion

  // A continuation for synthesizing the "larger" statement from substatement
  type StmtProducer = Seq[Statement] => Statement

  abstract sealed class RuleResult
  /**
    * A result of an inductive rule application:
    * - a sequence of subgoals for the engine
    * - a producer, continuation that will combine their results into the final statement
    * the empty list of subgoals paired with an identity procuder would mean an end of synthesis
    */
  case class MoreGoals(goals: Seq[Spec], kont: StmtProducer) extends RuleResult

  /**
    * A result of a rule with no sub-goals: just return the last statement
    */
  case class LastStatement(st: Statement) extends RuleResult

  /**
    * A generic class for a deductive rule to be applied
    */
  abstract sealed class Rule {
    // Is this rule applicable at all?
    def isApplicable(spec: Spec): Boolean

    // Apply the rule and get the subgoals
    def apply(spec: Spec): RuleResult
  }

  ///////////////////////////////////////////////////////////////////
  ///////////              Specific rules                     ///////
  ///////////////////////////////////////////////////////////////////

  /*
  Empty rule: supposed to be applied at the end

      ---------------------------------------- [emp]
      Γ ; { emp } ; { emp } ---> return;
  */

  object EmpRule extends Rule {
    def isApplicable(spec: Spec): Boolean = {
      // TODO: Ignore the pure parts for now
      // TODO: Replace this by a general entailment checker

      spec.pre.sigma |- spec.post.sigma
    }

    def apply(spec: Spec): RuleResult = {
      // TODO: add value-returning statements

      LastStatement(Return(None))
    }
  }


  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{ φ ; x -> A * P } ; [y/A]{ ψ ; Q } ---> S
      ---------------------------------------------------------------------- [read]
              Γ ; { φ ; x -> A * P } ; { ψ ; Q } ---> let y := *x ; S
  */

  object ReadRule extends Rule {
    def isApplicable(spec: Spec): Boolean = {
      spec.pre.sigma.getHeadHeaplet match {
        case Some(PointsTo(_, _, a@(Var(_)))) =>
          spec.isGhost(a) && spec.getType(a).nonEmpty
        case _ => false
      }
    }

    def apply(spec: Spec): RuleResult = {
      /*
      TODO:
      1. Generate fresh variable (wrt. gamma)
      2. Change the spec for the goal
      3. Make a continuation for wrapping the rest
       */



      ???
    }
  }

}
