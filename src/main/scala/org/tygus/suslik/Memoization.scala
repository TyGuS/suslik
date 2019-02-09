package org.tygus.suslik

import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SynthesisRule
import org.tygus.suslik.util.SynStats

import scala.collection.mutable

trait Memoization {

  type ResultMap = mutable.Map[(Goal, List[SynthesisRule]), (Option[Statement], Int)]

  def runWithMemo(goal: Goal,
                  savedResults: ResultMap,
                  stats: SynStats,
                  rules: List[SynthesisRule],
                  res: => Option[Statement]): Option[Statement] = {
    if (!goal.env.config.memoization) {
      res
    } else if (savedResults.contains(goal, rules)) { //
      val (res, recalled_count) = savedResults(goal, rules)
      savedResults((goal, rules)) = (res, recalled_count + 1)
      logMemoization(stats, res)
      res
    } else {
      logMemoization(stats, res)
      savedResults((goal, rules)) = (res, 0)
      res
    }
  }

  private def logMemoization(stats: SynStats, res: Option[Statement]) = {
    if (res.isDefined) {
      stats.bumpUpRecalledResultsPositive()
    } else {
      stats.bumpUpRecalledResultsNegative()
    }
  }


}
