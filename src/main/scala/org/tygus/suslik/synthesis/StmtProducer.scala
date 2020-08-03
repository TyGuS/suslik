package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions.{Expr, Subst, SubstVar, Var}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.{Heaplet, InductiveClause, SApp, SFormula}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.synthesis.rules.RuleUtils

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

  def liftToSolutions(f: Seq[Statement] => Statement)(arg: Seq[Solution]): Solution = {
    val (stmts, helpers) = arg.unzip
    val stmt = f(stmts)
    val allHelpers = helpers.toList.flatten
    (stmt, allHelpers)
  }

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
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(s, stmts.head).simplify
  })
}

/**
  * Same as prepend but do not simplify s away, because it comes from the sketch
  */
case class PrependFromSketchProducer(s: Statement) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(s, stmts.head)
  })
}

/**
  * Producer that appends s to the first child solution
  */
case class AppendProducer(s: Statement) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(stmts.head, s).simplify
  })
}

/**
  * Producer that sequentially composes results of two goals
  */
case object SeqCompProducer extends StmtProducer {
  val arity: Int = 2
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(stmts.head, stmts.last).simplify
  })
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
      val newHelper = Procedure(f, stmt)
      (goal.toCall, newHelper :: helpers)
    } else
      (stmt, helpers)
  }
}

case class HandleGuard(goal: Goal) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    stmts.head match {
      case g@Guarded(cond, body, els, l) =>
        if (goal.label == l) If(cond, body, els).simplify // Current goal is the branching point: create conditional
        else g // Haven't reached the branching point yet: propagate guarded statement
      case stmt => stmt
    }
  })
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

trait Noop {
  val arity: Int = 1
  val fn: Kont = _.head
}

// Captures variable substitutions
case class SubstProducer(subst: Subst) extends StmtProducer with Noop

// Captures ghost variable instantiations
case class GhostSubstProducer(subst: SubstVar) extends StmtProducer with Noop

// Captures an unfolded predicate application
case class UnfoldProducer(app: SApp, selector: Expr, substPred: SubstVar, substEx: SubstVar, substArgs: Subst) extends StmtProducer with Noop
