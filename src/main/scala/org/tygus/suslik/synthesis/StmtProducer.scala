package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.rules.BranchRules.Branch
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
      // Substitute all unknowns with true
      val finalized = (f.pre.phi.unknowns ++ f.post.phi.unknowns).foldLeft(f)({case (spec, u) => spec.substUnknown(Map(u -> Expressions.eTrue))})
      val (newHelper, newCall) = Procedure(finalized, stmt).removeUnusedParams(goal.toCall)
      (newCall, newHelper.simplifyParams :: helpers)
    } else
      (stmt, helpers)
  }
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

// Joins a guarded statement and an else-branch into a conditional,
// if goal is the right branching point (otherwise simply propagates the guarded statement)
case class GuardedBranchProducer(goal: Goal) extends StmtProducer {
  val arity: Int = 2
  val fn: Kont = liftToSolutions(stmts => {
    stmts.head match {
      case Guarded(cond, body) if Branch.isBranchingPoint(goal, cond)
        => If(cond, body, stmts.last).simplify // Current goal is the branching point: create conditional
      case stmt => stmt // Current goal is not the branching point: second child is always vacuous, so ignore it
    }
  })
}

// Creates a guarded statement with condition cond
case class GuardedProducer(cond: Expr) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => Guarded(cond, stmts.head))
}

// Captures the existential substitution map produced by the Pick rule
case class ExistentialProducer(subst: Map[Var, Expr]) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => stmts.head)
}


