package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.{Heaplet, PureLogicUtils, SApp}
import org.tygus.suslik.logic.Specifications.{Derivation, Goal, RuleApplication}

object Rules {
  /**
    * A continuation that builds a solution for a synthesis problem
    * from solutions of its sub-problems
    */
  case class StmtProducer (arity: Int,
                           fn: Seq[Solution] => Solution,
                           source: String) extends RuleUtils {
    val exceptionQualifier: String = "producer"

    def apply(children: Seq[Solution]): Solution = {
      ruleAssert(children.lengthCompare(arity) == 0, s"Producer $source expects $arity children and got ${children.length}")
      fn(children)
    }

    /**
      * Producer transformer that sequences two producers:
      * the resulting producer first applies p1 to a prefix of child solutions,
      * then applies p2 to the result of p1 and a suffix of child solutions
      */
    def >>(p: StmtProducer): StmtProducer = StmtProducer (
      this.arity + p.arity - 1,
      sols => {
        val (sols1, sols2) = sols.splitAt(this.arity)
        val sol = this.fn(sols1)
        p.fn(sol +: sols2)
      },
      s"join-${this.source}-${p.source}"
    )
  }

  def liftToSolutions(f: Seq[Statement] => Statement)(arg: Seq[Solution]): Solution = {
    val (stmts, helpers) = arg.unzip
    val stmt = f(stmts)
    val allHelpers = helpers.toList.flatten
    (stmt,allHelpers)
  }

  /**
    * Identity producer: returns the first child solution unchanged
    */
  def idProducer(source: String): StmtProducer =
    StmtProducer(1, _.head, source)

  /**
    * Constant producer: ignored child solutions and returns s
    */
  def constProducer(s: Statement, source: String): StmtProducer =
    StmtProducer(0, liftToSolutions(_ => s), source)

  /**
    * Producer that prepends s to the first child solution
    */
  def prepend(s: Statement, source: String): StmtProducer =
    StmtProducer(1, liftToSolutions(stmts => {SeqComp(s, stmts.head).simplify}), source)

  /**
    * Producer that appends s to the first child solution
    */
  def append(s: Statement, source: String): StmtProducer =
    StmtProducer(1, liftToSolutions(stmts => {SeqComp(stmts.head, s).simplify}), source)

  /**
    * Producer that checks if the child solution has backlinks to its goal,
    * and if so produces a helper call and a new helper
    */
  def extractHelper(goal: Goal): StmtProducer = StmtProducer (
    1,
    sols => {
      val (stmt, helpers) = sols.head
      if (stmt.companions.contains(goal.label)) {
        val f = goal.toFunSpec
        val newHelper = Procedure(f.name, f.rType, f.params, stmt)
        (goal.toCall, newHelper :: helpers)
      } else
        (stmt, helpers)
    },
    "helper"
  )

  def handleGuard(goal: Goal): StmtProducer = StmtProducer (
    1,
    liftToSolutions(stmts => {stmts.head match {
      case g@Guarded(cond, body, els, l) =>
        if (goal.label == l) If(cond, body, els) // Current goal is the branching point: create conditional
        else g // Haven't reached the branching point yet: propagate guarded statement
      case stmt => stmt
    }}),
    "handleGuard"
  )

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
