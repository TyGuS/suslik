package org.tygus.synsl

import org.tygus.synsl.LanguageUtils.generateFreshVar
import org.tygus.synsl.language.Expressions.{Expr, Var}
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
    * Rule is not applicable
    */
  case class Fail() extends RuleResult

  /**
    * Rule is applicable and produces:
    * - a sequence of subgoals (premises fo the rule)
    * - a producer: continuation that combines the results of the subgoals into the final statement
    * An empty list of subgoals paired with an constant producer denotes a leaf in the synthesis derivation
    */
  case class MoreGoals(goals: Seq[Spec], kont: StmtProducer) extends RuleResult

  /**
    * A generic class for a deductive rule to be applied
    */
  abstract sealed class Rule extends RuleUtils {
    // Apply the rule and get the subgoals
    def apply(spec: Spec): RuleResult

  }

  ///////////////////////////////////////////////////////////////////
  ///////////              Specific rules                     ///////
  ///////////////////////////////////////////////////////////////////

  /*
  Empty rule: supposed to be applied at the end

                  P |- Q
      ---------------------------------------- [emp]
      Γ ; { true; P } ; { true; Q } ---> return;
  */

  object EmpRule extends Rule {

    override def toString: Ident = "[emp]"

    def apply(spec: Spec): RuleResult = {
      // TODO: add value-returning statements
      if (spec.pre.sigma |- spec.post.sigma)
        MoreGoals(Seq.empty[Spec], _ => {Return(None)})
      else Fail()
    }
  }


  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{ φ ; x -> A * P } ; [y/A]{ ψ ; Q } ---> S
      ---------------------------------------------------------------------- [read]
              Γ ; { φ ; x -> A * P } ; { ψ ; Q } ---> let y := *x ; S
  */
  object ReadRule extends Rule {

    def isGhostHeaplet(spec: Spec): SFormula => Boolean = {
      case PointsTo(id, offset, a@(Var(_))) => spec.isGhost(a)
      case _ => false
    }

    override def toString: Ident = "[read]"

    def apply(spec: Spec): RuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec
      val ghostHeaplets = spec.pre.sigma.findSubFormula(isGhostHeaplet(spec)).toList
      if (ghostHeaplets.isEmpty) return Fail()

      val PointsTo(x, offset, a@(Var(_))) = ghostHeaplets.head
      val y = generateFreshVar(spec, a.name)

      assert(spec.getType(a).nonEmpty, s"Cannot derive a type for the ghost variable $a in spec ${spec.pp}")
      val tpy = spec.getType(a).get

      val subGoalSpec = Spec(pre.subst(a, y), post.subst(a, y), (tpy, y) :: gamma.toList)
      val kont: StmtProducer = stmts => {
        assert(stmts.lengthCompare(1) == 0, s"Read rule expected 1 premise and got ${stmts.length}")
        val rest = stmts.head
        // Do not generate read for unused variables
        if (rest.usedVars.contains(y)) Load(y, tpy, x, offset, rest) else rest
      }

      MoreGoals(Seq(subGoalSpec), kont)
    }
  }

  /*
  Write rule: create a new write from where it's possible

                      Γ ; { φ ; P } ; { ψ ; Q } ---> S
      -------------------------------------------------------------- [write]
       Γ ; { φ ; x -> e1 * P } ; { ψ ; x -> e2 * Q } ---> *x := e2 ; S
   */
  object WriteRule extends Rule {

    override def toString: Ident = "[write]"

    def apply(spec: Spec): RuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec
      val heaplets = heapletsForWrite(spec)
      if (heaplets.isEmpty) return Fail()

      val (h1@PointsTo(x, ox, _), h2@PointsTo(_, _, e2: Expr)) = heaplets.head

      val subGoalSpec = Spec(pre.removeSubformula(_ == h1), post.removeSubformula(_ == h2), gamma)
      val kont: StmtProducer = stmts => {
        assert(stmts.lengthCompare(1) == 0, s"Write rule expected 1 premise and got ${stmts.length}")
        val rest = stmts.head
        Store(x, ox, e2, rest)
      }

      MoreGoals(Seq(subGoalSpec), kont)
    }

  }

  /*
  Frame rule: reduce the size of the specification
  TODO: generalize from just heaplets

        (GV(Q) / GV(P)) ∪ GV(R) = Ø
      Γ ; { φ ; P } ; { ψ ; Q } ---> S
    ---------------------------------------- [frame]
    Γ ; { φ ; P * R } ; { ψ ; Q * R } ---> S

   */
  object FrameRule extends Rule {

    override def toString: Ident = "[frame]"

    def apply(spec: Spec): RuleResult = {
      val heaplets = heapletsForFrame(spec)
      if (heaplets.isEmpty) return Fail()

      val (p1, p2) = heaplets.head
      val Spec(pre, post, gamma: Gamma) = spec

      val subGoalSpec = Spec(pre.removeSubformula(_ == p1), post.removeSubformula(_ == p2), gamma)
      val kont: StmtProducer = stmts => {
        assert(stmts.lengthCompare(1) == 0, s"Frame rule expected 1 premise and got ${stmts.length}")
        stmts.head
      }

      MoreGoals(Seq(subGoalSpec), kont)
    }

  }


}

