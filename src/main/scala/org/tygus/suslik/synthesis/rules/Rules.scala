package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.{Expr}
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications.{Footprint, Goal}

object Rules {
  /**
    * A continuation that builds a solution for a synthesis problem
    * from solutions of its sub-problems
    */
  case class StmtProducer (arity: Int,
                           fn: Seq[Solution] => Solution) extends RuleUtils {
    val exceptionQualifier: String = "producer"

    def apply(children: Seq[Solution]): Solution = {
      ruleAssert(children.lengthCompare(arity) == 0, s"Producer expects $arity children and got ${children.length}")
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
      }
    )

    /**
      * Producer that results form partially applying this producer to s
      */
    def partApply(s: Solution): StmtProducer = StmtProducer (
      this.arity - 1,
      sols => {
        this.apply(s +: sols)
      }
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
  def idProducer: StmtProducer =
    StmtProducer(1, _.head)

  /**
    * Constant producer: ignored child solutions and returns s
    */
  def constProducer(s: Statement): StmtProducer =
    StmtProducer(0, liftToSolutions(_ => s))

  /**
    * Producer that prepends s to the first child solution
    */
  def prepend(s: Statement): StmtProducer =
    StmtProducer(1, liftToSolutions(stmts => {SeqComp(s, stmts.head).simplify}))

  /**
    * Same as prepend but do not simplify s away, because it comes from the sketch
    */
  def prependFromSketch(s: Statement): StmtProducer =
    StmtProducer(1, liftToSolutions(stmts => {SeqComp(s, stmts.head)}))

  /**
    * Producer that appends s to the first child solution
    */
  def append(s: Statement): StmtProducer =
    StmtProducer(1, liftToSolutions(stmts => {SeqComp(stmts.head, s).simplify}))

  /**
    * Producer that sequentially composes results of two goals
    */
  def seqComp: StmtProducer =
    StmtProducer(2, liftToSolutions (stmts => {SeqComp(stmts.head, stmts.last).simplify}))

  /**
    * Producer that checks if the child solution has backlinks to its goal,
    * and if so produces a helper call and a new helper
    */
  def extractHelper(goal: Goal): StmtProducer = StmtProducer (
    1,
    sols => {
      val (stmt, helpers) = sols.head
      if (stmt.companions.contains(goal.label) && !goal.isTopLevel) {
        val f = goal.toFunSpec
        val newHelper = Procedure(f.name, f.rType, f.params, stmt)
        (goal.toCall, newHelper :: helpers)
      } else
        (stmt, helpers)
    }
  )

  def handleGuard(goal: Goal): StmtProducer = StmtProducer (
    1,
    liftToSolutions(stmts => {stmts.head match {
      case g@Guarded(cond, body, els, l) =>
        if (goal.label == l) If(cond, body, els) // Current goal is the branching point: create conditional
        else g // Haven't reached the branching point yet: propagate guarded statement
      case stmt => stmt
    }})
  )

  // Produces a conditional that branches on the selectors
  def branchProducer(selectors: Seq[Expr]): StmtProducer = StmtProducer (
    selectors.length,
    liftToSolutions (stmts => {
      if (stmts.length == 1) stmts.head else {
        val cond_branches = selectors.zip(stmts).reverse
        val ctail = cond_branches.tail
        val finalBranch = cond_branches.head._2
        ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => If(c, tb, eb).simplify }
      }
    })
  )


  /**
    * Result of a rule application:
    * sub-goals to be solved and
    * a statement producer that assembles the sub-goal results
    */
  case class RuleResult(subgoals: Seq[Goal], kont: StmtProducer, consume: Footprint, rule: SynthesisRule)
    extends PrettyPrinting with PureLogicUtils {

    override def pp: String = rule.toString // s"[${subgoals.map(_.label.pp).mkString(", ")}]"
  }

  /**
    * A generic class for a deductive rule to be applied
    *
    * @author Ilya Sergey
    */
  abstract class SynthesisRule extends PureLogicUtils {
    // Apply the rule and get all possible sub-derivations
    def apply(goal: Goal): Seq[RuleResult]
  }

  /**
    * Different kinds of rules
    */

  // Invertible rule: does not restrict the set of derivations,
  // so no need to backtrack in case of failure
  trait InvertibleRule

  trait UnfoldingPhase {
    def heapletFilter(h: Heaplet): Boolean = {
      h.isInstanceOf[SApp]
    }
  }

  trait BlockPhase {
    def heapletFilter(h: Heaplet): Boolean = {
      h.isInstanceOf[Block]
    }
  }

  trait FlatPhase {
    def heapletFilter(h: Heaplet): Boolean = true
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
