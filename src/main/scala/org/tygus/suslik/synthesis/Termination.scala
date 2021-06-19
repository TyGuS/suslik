package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions.{BinaryExpr, OpLt, Var}
import org.tygus.suslik.language.{CardType, PrettyPrinting}
import org.tygus.suslik.logic.Specifications.{Goal, GoalLabel}
import org.tygus.suslik.logic.smt.CyclicProofChecker
import org.tygus.suslik.report.Log
import org.tygus.suslik.synthesis.SearchTree.{AndNode, OrNode}
import org.tygus.suslik.util.SynStats

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
      pairs.map { case (v1, v2) => s"(${v1.pp}, ${v2.pp})" }.mkString(", ")

    override def pp: String =
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
  def collectTrace(leaves: List[OrNode], newTransitions: Seq[Transition] = List()): Seq[Transition] = {
    def traceFrom(leaf: OrNode): List[Transition] = leaf.andAncestors.flatMap(_.transitions)

    (leaves.flatMap(traceFrom) ++ newTransitions).distinct.sorted
  }

  // Checks that the proof generated so far in the same branch of the search as andNode
  // satisfies the global soundness condition of cyclic proofs after adding new transitions of the andNode
  def isTerminatingExpansion(andNode: AndNode)(implicit log: Log, config: SynConfig, stats: SynStats): Boolean = {
    if (andNode.transitions.exists(_.isBacklink)) {
        // Construct the trace using only success leaves from my branch of the search and my own proof branch
        val relevantSuccessLeaves = andNode.parent.partialDerivation
        val trace = collectTrace(andNode.parent :: relevantSuccessLeaves, andNode.transitions)
//        log.print(List((s"New backlink formed by ${andNode.rule}", Console.CYAN)))
//        log.print(List((s"${trace.map(_.pp).mkString("\n")};", Console.CYAN)))
        val traceToCheck = s"${trace.map(_.pp).mkString("\n")};"
        stats.recordCyclistTime(CyclicProofChecker.checkProof(traceToCheck))
    }
    else true // This expansion does not form a backlink, so cannot break termination
  }

}
