package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications.{Footprint, Goal}

object Rules {
  type Kont = Seq[Solution] => Solution

  /**
    * A continuation that builds a solution for a synthesis problem
    * from solutions of its sub-problems
    */
  sealed abstract class StmtProducer extends RuleUtils {
    val exceptionQualifier: String = "producer"

    val arity: Int
    val fn: Kont

    def apply(children: Seq[Solution]): Solution = {
      ruleAssert(children.lengthCompare(arity) == 0, s"Producer expects $arity children and got ${children.length}")
      fn(children)
    }

    /**
      * Producer transformer that sequences two producers:
      * the resulting producer first applies p1 to a prefix of child solutions,
      * then applies p2 to the result of p1 and a suffix of child solutions
      */
    def >>(p: StmtProducer): StmtProducer = ChainedProducer(this, p)

    /**
      * Producer that results form applying this producer to s as its idx argument
      */
    def partApply(s: Solution): StmtProducer = PartiallyAppliedProducer(this, s)
  }

  def liftToSolutions(f: Seq[Statement] => Statement)(arg: Seq[Solution]): Solution = {
    val (stmts, helpers) = arg.unzip
    val stmt = f(stmts)
    val allHelpers = helpers.toList.flatten
    (stmt,allHelpers)
  }

  case class ChainedProducer(p1: StmtProducer, p2: StmtProducer) extends StmtProducer {
    val arity: Int = p1.arity + p2.arity - 1
    val fn: Kont = sols => {
      val (sols1, sols2) = sols.splitAt(p1.arity)
      val sol = p1.fn(sols1)
      p2.fn(sol +: sols2)
    }
  }

  case class PartiallyAppliedProducer(p: StmtProducer, s: Solution) extends StmtProducer {
    val arity: Int = p.arity - 1
    val fn: Kont = sols => {
      p.apply(s +: sols)
    }
  }

  /**
    * Identity producer: returns the first child solution unchanged
    */
  case object IdProducer extends StmtProducer {
    val arity: Int = 1
    val fn: Kont = _.head
  }

  /**
    * Constant producer: ignored child solutions and returns s
    */
  case class ConstProducer(s: Statement) extends StmtProducer {
    val arity: Int = 0
    val fn: Kont = liftToSolutions(_ => s)
  }

  /**
    * Producer that prepends s to the first child solution
    */
  case class PrependProducer(s: Statement) extends StmtProducer {
    val arity: Int = 1
    val fn: Kont = liftToSolutions(stmts => { SeqComp(s, stmts.head).simplify })
  }

  /**
    * Same as prepend but do not simplify s away, because it comes from the sketch
    */
  case class PrependFromSketchProducer(s: Statement) extends StmtProducer {
    val arity: Int = 1
    val fn: Kont = liftToSolutions(stmts => { SeqComp(s, stmts.head) })
  }

  /**
    * Producer that appends s to the first child solution
    */
  case class AppendProducer(s: Statement) extends StmtProducer {
    val arity: Int = 1
    val fn: Kont = liftToSolutions(stmts => { SeqComp(stmts.head, s).simplify })
  }

  /**
    * Producer that sequentially composes results of two goals
    */
  case object SeqCompProducer extends StmtProducer {
    val arity: Int = 2
    val fn: Kont = liftToSolutions(stmts => {SeqComp(stmts.head, stmts.last).simplify})
  }

  /**
    * Producer that checks if the child solution has backlinks to its goal,
    * and if so produces a helper call and a new helper
    */
  case class ExtractHelper(goal: Goal) extends StmtProducer {
    val arity: Int = 1
    val fn: Kont = sols => {
      val (stmt, helpers) = sols.head
      if (stmt.companions.contains(goal.label) && !goal.isTopLevel) {
        val f = goal.toFunSpec
        val newHelper = Procedure(f.name, f.rType, f.params, stmt)
        (goal.toCall, newHelper :: helpers)
      } else
        (stmt, helpers)
    }
  }

  case class HandleGuard(goal: Goal) extends StmtProducer {
    val arity: Int = 1
    val fn: Kont = liftToSolutions(stmts => {stmts.head match {
      case g@Guarded(cond, body, els, l) =>
        if (goal.label == l) If(cond, body, els).simplify // Current goal is the branching point: create conditional
        else g // Haven't reached the branching point yet: propagate guarded statement
      case stmt => stmt
    }})
  }

  // Produces a conditional that branches on the selectors
  case class BranchProducer(selectors: Seq[Expr]) extends StmtProducer {
    val arity: Int = selectors.length
    val fn: Kont = liftToSolutions(stmts => {
      if (stmts.length == 1) stmts.head else {
        val cond_branches = selectors.zip(stmts).reverse
        val ctail = cond_branches.tail
        val finalBranch = cond_branches.head._2
        ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => If(c, tb, eb).simplify }
      }
    })
  }

  case class GuardedProducer(cond: Expr, goal: Goal) extends StmtProducer {
    val arity: Int = 2
    val fn: Kont = liftToSolutions(stmts => Guarded(cond, stmts.head, stmts.last, goal.label))
  }

  // Captures the existential substitution map produced by the Pick rule
  case class ExistentialProducer(subst: Map[Var, Expr]) extends StmtProducer {
    val arity: Int = 1
    val fn: Kont = liftToSolutions(stmts => stmts.head)
  }


  /**
    * Result of a rule application:
    * sub-goals to be solved and
    * a statement producer that assembles the sub-goal results
    */
  case class RuleResult(subgoals: Seq[Goal], kont: StmtProducer, consume: Footprint, rule: SynthesisRule)
    extends PrettyPrinting with PureLogicUtils {

    override def pp: String = rule.toString // s"[${subgoals.map(_.label.pp).mkString(", ")}]"

    def produces(parent: Goal): Seq[Footprint] = subgoals.map(g => g.allHeaplets - (parent.allHeaplets - consume))
  }

  /**
    * A generic class for a deductive rule to be applied
    *
    * @author Ilya Sergey
    */
  abstract class SynthesisRule extends PureLogicUtils {
    // Apply the rule and get all possible sub-derivations
    def apply(goal: Goal): Seq[RuleResult]

    def cost: Int = 0
  }

  /**
    * Different kinds of rules
    */

  // Invertible rule: does not restrict the set of derivations,
  // so no need to backtrack in case of failure
  trait InvertibleRule

  // This rule produces code
  trait GeneratesCode

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
