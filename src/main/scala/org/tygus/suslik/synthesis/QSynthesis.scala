package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.util.SynStats

import scala.Console._
import scala.annotation.tailrec
import scala.collection.mutable

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait QSynthesis extends Synthesis {

  protected override def synthesize(goal: Goal, depth: Int) // todo: add goal normalization
                          (stats: SynStats)
                          (implicit ind: Int = 0,
                           savedResults: ResultMap = mutable.Map.empty): Option[Solution] = {
    // Initialize worklist with a single subderivation
    // whose sole open goal is the top-level goal
    val worklist = Vector(Subderivation(List(goal), idProducer("init")))
    processWorkList(worklist)(stats, goal.env.config, ind)
  }

  @tailrec
  private def processWorkList(worklist: Seq[Subderivation])
                            (implicit
                             stats: SynStats,
                             config: SynConfig,
                             ind: Int): Option[Solution] = {

    // Check for timeouts
    val currentTime = System.currentTimeMillis()
    if (currentTime - config.startTime > config.timeOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut.toDouble / 1000} seconds.\n")
    }

    printLog(List((s"\nWorklist size: ${worklist.length}", Console.YELLOW)))

    worklist match {
      case Nil =>
        // No more subderivations to try: synthesis failed
        None
      case subderiv +: rest => subderiv.subgoals match {
        // Otherwise pick a subderivation to expand
        case Nil =>
          // This subderivation has no open goals: synthesis succeeded, build the solution
          Some(subderiv.kont(Nil))
        case goal :: moreGoals => {
          // Otherwise, expand the first open goal
          printLog(List((s"Goal to expand: ${goal.label.pp}", Console.BLUE)))
          if (config.printEnv) {
            printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
          }
          printLog(List((s"${goal.pp}", Console.BLUE)))

          // Apply all possible rules to the current goal to get a list of alternatives,
          // each of which can have multiple open goals
          val rules = nextRules(goal, 0)
          val children =
            if (goal.isUnsolvable) Nil  // This is a special unsolvable goal, discard eagerly
            else applyRules(rules)(goal, stats, config, ind)

          if (children.isEmpty) {
            stats.bumpUpBacktracing()
            printLog(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
          }

          // To turn those alternatives into valid subderivations,
          // add the rest of the open goals from the current subderivation,
          // and set up the solution producer to join results from all the open goals
          val newSubderivations = children.map(child =>
            Subderivation(child.subgoals ++ moreGoals, child.kont >> subderiv.kont))
          // Add new subderivations to the worklist and process
          processWorkList(newSubderivations ++ rest)
        }
      }
    }
  }

  protected def applyRules(rules: List[SynthesisRule])(implicit goal: Goal,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ind: Int): Seq[Subderivation] = rules match
  {
    case Nil => Vector() // No more rules to apply: done expanding the goal
    case r :: rs =>
      val goalStr = s"$r: "
      // Invoke the rule
      val allChildren = r(goal)
      // Filter out children that contain out-of-order goals
      val children = if (config.commute) {
        allChildren.filterNot(_.subgoals.exists(goalOutOfOrder))
      } else allChildren

      if (children.isEmpty) {
        // Rule not applicable: try other rules
        printLog(List((s"${goalStr}FAIL", BLACK)), isFail = true)
        applyRules(rs)
      } else {
        // Rule applicable: try all possible sub-derivations
        val subSizes = children.map(c => s"${c.subgoals.size} sub-goal(s)").mkString(", ")
        val succ = s"SUCCESS at depth $ind, ${children.size} alternative(s) [$subSizes]"
        printLog(List((s"$goalStr$GREEN$succ", BLACK)))
        stats.bumpUpSuccessfulRuleApp()
        if (config.invert && r.isInstanceOf[InvertibleRule]) {
          // The rule is invertible: do not try other rules on this goal
          children
        } else {
          // Both this and other rules apply
          children ++ applyRules(rs)
        }
      }
  }

  // Is current goal supposed to appear before g?
  def goalOutOfOrder(g: Goal)(implicit goal: Goal,
                           stats: SynStats,
                           config: SynConfig,
                           ind: Int): Boolean = {
    g.deriv.outOfOrder(allRules(goal)) match {
      case None => false
      case Some(app) =>
        //              printLog(List((g.deriv.preIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        //              printLog(List((g.deriv.postIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        printLog(List((s"${RED}Alternative ${g.deriv.applications.head.pp} commutes with earlier ${app.pp}", BLACK)))
        true
    }
  }

}