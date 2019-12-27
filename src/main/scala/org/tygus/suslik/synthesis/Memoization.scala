package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.Statements.{Solution, Statement}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, Transition, mkSFormula}
import org.tygus.suslik.synthesis.Memoization.{PrecursorMap, ResultMap}
import org.tygus.suslik.synthesis.SearchTree.{NodeId, OrNode}

import scala.collection.mutable

object Memoization {
  // Simplified, canonical goal for memoization
  case class MemoGoal(pre: Assertion,
                      post: Assertion,
                      programVars: Set[Var],
                      universalGhosts: Set[Var],
                      sketch: Statement)

  sealed abstract class GoalStatus
  case class Failed() extends GoalStatus
  case class Succeeded(sol: Solution) extends GoalStatus
  case class Expanded() extends GoalStatus

  class ResultMap {
    private val memo: mutable.Map[MemoGoal, GoalStatus] = mutable.Map.empty

    def size: Int = memo.size

    def clear(): Unit = {
      memo.clear()
    }

    def lookup(goal: Goal): Option[GoalStatus] = {
      memo.get(trimGoal(goal))
    }

    def save(goal: Goal, status: GoalStatus): Unit = {
      memo(trimGoal(goal)) = status
    }

    private def trimGoal(g: Goal): MemoGoal = MemoGoal(
      Assertion(g.pre.phi, mkSFormula(g.pre.sigma.chunks.sorted)),
      Assertion(g.post.phi, mkSFormula(g.post.sigma.chunks.sorted)),
      g.programVars.toSet,
      g.universalGhosts,
      g.sketch)

  }

  // For each or-node, transitions that have been tried before and failed;
  // i.e. transitions of its older siblings
  class PrecursorMap {
    private val precMap: mutable.Map[NodeId, Set[Transition]] = mutable.Map.empty

    def clear(root: OrNode): Unit = {
      precMap.clear()
      precMap(root.id) = Set()
    }

    def save(n: NodeId, precs: Set[Transition]): Unit = {
      // If this node has younger and-siblings, do not add any precursors:
      // the precursor might have failed because of its younger sibling
      // and not because of n!
      precMap(n) = if (n.head <= 0) precs else Set()
    }

    def subsumer(n: OrNode, by: OrNode): Option[OrNode] = {
      by.commuters(n.transition).find(com => precMap(com.id).exists(_.equivalent(n.transition)))
    }

    def removeDescendants(n: NodeId): Unit = {
      precMap.retain((i, _) => !i.endsWith(n))
    }
  }
}

trait HasMemo {
  implicit val precursors: PrecursorMap = new PrecursorMap()
  implicit val memo: ResultMap = new ResultMap()

  def clearMemo(root: OrNode): Unit = {
    memo.clear()
    precursors.clear(root)
  }
}
