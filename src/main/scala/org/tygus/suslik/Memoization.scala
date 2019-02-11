package org.tygus.suslik

import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SynthesisRule
import org.tygus.suslik.util.SynStats

import scala.collection.mutable

class Memoization {

  type ResultMap = mutable.Map[(Goal, List[SynthesisRule]), (Option[Statement], Int)]

  val savedResults: ResultMap = mutable.Map.empty

  def cleanup() = savedResults.clear()

  def runWithMemo(goal: Goal,
                  stats: SynStats,
                  rules: List[SynthesisRule],
                  res: => Option[Statement]): Option[Statement] = {
    if (!goal.env.config.memoization) {
      res
    } else if (savedResults.contains(goal, rules)) { //
      val (res, recalled_count) = savedResults(goal, rules)
      savedResults((goal, rules)) = (res, recalled_count + 1)
      logMemoizationRecalled(stats, res)
      res
    } else {
      logMemoizationSaved(stats, res)
      savedResults((goal, rules)) = (res, 0)
      res
    }
  }

  private def logMemoizationRecalled(stats: SynStats, res: Option[Statement]) = {
    if (res.isDefined) {
      stats.bumpUpRecalledResultsPositive()
    } else {
      stats.bumpUpRecalledResultsNegative()
    }
  }

  private def logMemoizationSaved(stats: SynStats, res: Option[Statement]) = {
    if (res.isDefined) {
      stats.bumpUpSavedResultsPositive()
    } else {
      stats.bumpUpSavedResultsNegative()
    }
  }


}
