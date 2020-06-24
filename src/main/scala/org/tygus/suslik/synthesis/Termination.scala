package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions.{BinaryExpr, OpLt, Var}
import org.tygus.suslik.language.{CardType, PrettyPrinting}
import org.tygus.suslik.logic.Specifications.{Goal, GoalLabel}
import org.tygus.suslik.synthesis.SearchTree.OrNode

object Termination {

  // Pair of cardinality variables
  type TracePair = (Var, Var)

  /**
    * Which pairs of cardinality variables strictly decrease (progressing) vs non-strictly decrease (non-progressing)
    * between a goal and a subgoal
    */
  case class Transition(from: GoalLabel,
                        to: GoalLabel,
                        progressing: List[TracePair],
                        nonProgressing: List[TracePair]) extends PrettyPrinting with Ordered[Transition] {
    // Is this transition a cyclic backlink?
    def isBacklink: Boolean = to < from

    private def showTracePairs(pairs: List[TracePair]): String =
      pairs.map { case (v1, v2) => s"(${v1.pp}, ${v2.pp})"}.mkString(", ")

    override def pp : String =
      s"${from.pp} -> ${to.pp} : {${showTracePairs(progressing)}}, {${showTracePairs(nonProgressing)}}"

    override def compare(that: Transition): Int = (from, to).compare(that.from, that.to)
  }

  object Transition {
    // Default transition between a goal and subgoal:
    // assumes the variable names have the same meaning between the two goals.
    // This should not be used for backlinks.
    def apply(goal: Goal, subgoal: Goal): Transition = {
      // TODO: beef up with SMT reasoning if we want to support different card constraints
      val strictInequalities = for {
        BinaryExpr(OpLt, v1@Var(_), v2@Var(_)) <- subgoal.pre.phi.conjuncts.toList
        if v1.getType(subgoal.gamma).contains(CardType)
        if v2.getType(subgoal.gamma).contains(CardType)
        if goal.pre.vars.contains(v2)
      } yield (v2, v1)
      val sharedCardVars = for {
        v <- subgoal.vars.toList
        if v.getType(subgoal.gamma).contains(CardType)
        if goal.pre.vars.contains(v)
      } yield (v, v)
      new Transition(goal.label, subgoal.label, strictInequalities, sharedCardVars)
    }
  }

  // Collect all transition from nodes reachable from leaves
  def collectTrace(leaves: List[OrNode]): Seq[Transition] = {
    def traceFrom(leaf: OrNode): List[Transition] = leaf.andAncestors.flatMap(_.transitions)
    leaves.flatMap(traceFrom).distinct.sorted
  }

}
