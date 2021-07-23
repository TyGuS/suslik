package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.Statements.{Solution, Statement}
import org.tygus.suslik.logic.Gamma
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, GoalLabel, SuspendedCallGoal, mkSFormula}
import org.tygus.suslik.synthesis.SearchTree.{NodeId, OrNode}

import scala.collection.mutable
import scala.util.DynamicVariable

object Memoization {
  /**
    * Simplified, canonical goal for memoization
    */
  case class MemoGoal(pre: Assertion,
                      post: Assertion,
                      gamma: Gamma,
                      programVars: Set[Var],
                      universalGhosts: Set[Var],
                      sketch: Statement,
                      callGoal: Option[SuspendedCallGoal],
                      isCompanion: Boolean,
                      companionCands: List[GoalLabel])

  /**
    * What has the search discovered about a goal so far?
    */
  sealed abstract class GoalStatus
  // This goal has been fully explored and failed
  case object Failed extends GoalStatus
  // This goal has been fully explored and produces solution `sol`
  case class Succeeded(sol: Solution, nodeId: NodeId) extends GoalStatus
  // This goal has been expanded but not yet fully explored
  // (its descendants are still in the worklist)
  case object Expanded extends GoalStatus

  /**
    * Caches search results for goals
    */
  class Memo {
    // Maps goals we have seen to their search status
    private val cache: mutable.Map[MemoGoal, GoalStatus] = mutable.Map.empty
    // Maps expanded goals to equivalent ones that have been suspended waiting for this one to resolve
    private val suspended: mutable.Map[MemoGoal, Set[NodeId]] = mutable.Map.empty.withDefaultValue(Set())

    // For logging purposes
    def size: (Int, Int, Int) = (
      cache.count(_._2 == Failed),
      cache.count(_._2.isInstanceOf[Succeeded]),
      cache.count(_._2 == Expanded)
      )

    // Empty memo
    def clear(): Unit = {
      cache.clear()
      suspended.clear()
    }

    // Lookup goal in the cache
    def lookup(goal: Goal): Option[GoalStatus] = {
      cache.get(trimGoal(goal))
    }

    // Save search status of a goal
    def save(goal: Goal, status: GoalStatus)(implicit config: SynConfig): Unit = if (config.memoization) {
      val key = trimGoal(goal)
      cache(key) = status
      status match {
        case Failed => suspended.remove(key)
        case Succeeded(_, _) => suspended.remove(key)
        case _ =>
      }
    }

    // Forget a goal if it is expanded (but not resolved)
    // Useful when we abandon a branch of search without resolving all goals,
    // so now it's time for their suspended twins to shine.
    def forgetExpanded(goal: Goal): Unit = {
      val key = trimGoal(goal)
      cache.get(key) match {
        case Some(Expanded) => {
          cache.remove(key)
          suspended.remove(key)
        }
        case _ =>
      }
    }

    def suspend(node: OrNode)(implicit config: SynConfig): Unit = if (config.memoization) {
      val key = trimGoal(node.goal)
      suspended(key) = suspended(key) + node.id
    }

    def isSuspended(node: OrNode): Boolean = {
      suspended.values.exists(_.contains(node.id))
    }

    def suspendedSize: Int = suspended.size

    private def trimGoal(g: Goal): MemoGoal = {
      val usedVars = g.pre.vars ++ g.post.vars ++ g.sketch.vars
      MemoGoal(
        Assertion(g.pre.phi, mkSFormula(g.pre.sigma.chunks)),
        Assertion(g.post.phi, mkSFormula(g.post.sigma.chunks)),
        g.gamma.filterKeys(usedVars),
        g.programVars.toSet.intersect(usedVars),
        g.universalGhosts.intersect(usedVars),
        g.sketch,
        g.callGoal,
        g.isCompanion,
        g.companionCandidates.map(_.label)
      )
    }

  }

  // need to be thread-local, for `SynthesisServer`
  implicit def memo: Memo = _current.value
  private val _current = new DynamicVariable[Memo](new Memo())

  def init(): Unit = {
    _current.value = new Memo()
  }
}