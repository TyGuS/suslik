package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements.{SeqComp, Solution, Statement}
import org.tygus.suslik.logic.{Heaplet, PureLogicUtils, SApp}
import org.tygus.suslik.logic.Specifications.{Derivation, Goal, RuleApplication}

object Rules {
  /**
    * A continuation that builds a solution for a synthesis problem
    * from solutions of its sub-problems
    */
  case class StmtProducer (arity: Int,
                           fn: Seq[Statement] => Statement,
                           ruleName: String) extends RuleUtils {
    val exceptionQualifier: String = "producer"

    def apply(children: Seq[Solution]): Solution = {
      ruleAssert(children.lengthCompare(arity) == 0, s"Rule $ruleName expects $arity premise(s) and got ${children.length}")
      val (stmts, helpers) = children.unzip
      val stmt = fn(stmts)
      val allHelpers = helpers.toList.flatten

      (stmt,allHelpers)
    }
  }

  def idProducer(rulename: String): StmtProducer =
    StmtProducer(1, _.head, rulename)

  def constProducer(s: Statement, rulename: String): StmtProducer =
    StmtProducer(0, _ => s, rulename)

  def prepend(s: Statement, rulename: String): StmtProducer =
    StmtProducer(1, stmts => {SeqComp(s, stmts.head).simplify}, rulename)

  def append(s: Statement, rulename: String): StmtProducer =
    StmtProducer(1, stmts => {SeqComp(stmts.head, s).simplify}, rulename)

  def join(kont1: StmtProducer, kont2: StmtProducer): StmtProducer = StmtProducer (
    kont1.arity + kont2.arity - 1,
    stmts => {
      val (stmts1, stmts2) = stmts.splitAt(kont1.arity)
      val stmt = kont1.fn(stmts1)
      kont2.fn(stmt +: stmts2)
    },
    s"join-${kont1.ruleName}-${kont2.ruleName}")

  /**
    * An incomplete derivation:
    * consists of sub-goals (open leaves of the derivation) and
    * a statement producer that assembles the sub-goal results
    */
  case class Subderivation(subgoals: Seq[Goal], kont: StmtProducer)
    extends PrettyPrinting with PureLogicUtils {

    override def pp: String =
      s"${subgoals.size} subgoal(s):\n${subgoals.map { g => s"${g.env.pp}${g.pp}" }.mkString("\n")}"
  }

  /**
    * A generic class for a deductive rule to be applied
    *
    * @author Ilya Sergey
    */
  abstract class SynthesisRule extends PureLogicUtils {
    // Apply the rule and get all possible sub-derivations
    def apply(goal: Goal): Seq[Subderivation]

    // Is the rule enabled on this goal?
    def enabled(goal: Goal): Boolean

    def saveApplication(footprint: (Set[Int], Set[Int]),
                        currentDeriv: Derivation,
                        cost: Int = 0): RuleApplication =
      RuleApplication(this, footprint, (currentDeriv.preIndex.length, currentDeriv.postIndex.length), cost)
  }

  /**
    * Different kinds of rules
    */

  // Invertible rule: does not restrict the set of derivations,
  // so no need to backtrack in case of failure
  trait InvertibleRule

  trait AnyPhase {
    def enabled(goal: Goal): Boolean = true
  }

  trait UnfoldingPhase {
    def enabled(goal: Goal): Boolean = {
      goal.hasPredicates
    }

    def heapletFilter(h: Heaplet): Boolean = {
      h.isInstanceOf[SApp]
    }
  }

  trait FlatPhase {
    def enabled(goal: Goal): Boolean = {
      !goal.hasPredicates
    }

    def heapletFilter(h: Heaplet): Boolean = {
      true
    }
  }

  // Sort a sequence of alternative subderivations (where every subderivation contains a single goal)
  // by the footprint of their latest rule application,
  // so that sequential applications of the rule are unlikely to cause out-of-order derivations
  def sortAlternativesByFootprint(alts: Seq[Subderivation]): Seq[Subderivation] = {
    alts.sortBy(_.subgoals.head.deriv.applications.head)
  }

  def nubBy[A,B](l:List[A], p:A=>B):List[A] =
  {
    def go[A,B](l:List[A], p:A=>B, s:Set[B], acc:List[A]):List[A] = l match
    {
      case Nil => acc.reverse
      case x::xs if s.contains(p(x)) => go(xs,p,s,acc)
      case x::xs                     => go(xs,p,s+p(x),x::acc)
    }
    go(l,p,Set.empty,Nil)
  }
}
