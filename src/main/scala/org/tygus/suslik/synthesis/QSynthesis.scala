package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.rules.RuleUtils
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.util.SynStats

import scala.Console._
import scala.collection.mutable

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait QSynthesis extends Synthesis {

  protected override def synthesize(goal: Goal, depth: Int) // todo: add goal normalization
                          (stats: SynStats,
                           rules: List[SynthesisRule])
                          (implicit ind: Int = 0,
                           savedResults: ResultMap = mutable.Map.empty): Option[Solution] = {
    // Initialize worklist with a single subderivation
    // whose sole open goal is the top-level goal
    val worklist = Vector(Subderivation(List(goal), idProducer("init")))
    processWorkList(worklist)(stats, rules, goal.env.config, ind)
  }

  protected def processWorkList(worklist: Seq[Subderivation])
                            (implicit
                             stats: SynStats,
                             rules: List[SynthesisRule],
                             config: SynConfig,
                             ind: Int): Option[Solution] = {

    // Check for timeouts
    val currentTime = System.currentTimeMillis()
    if (currentTime - config.startTime > config.timeOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut.toDouble / 1000} seconds.\n")
    }

    worklist match {
      case Nil =>
        // No more subderivations to try: synthesis failed
        None
      case subderiv +: rest => subderiv.subgoals match {
        case Nil =>
          // This subderivation has no open goals: synthesis succeeded, build the solution
          Some(subderiv.kont(Nil))
        case goal :: moreGoals => { // This subderivation has open goals: pick one to expand
          if (config.printEnv) {
            printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
          }
          printLog(List((s"${goal.pp}", Console.BLUE)))

          // Apply all possible rules to the current goal to get a list of alternatives,
          // each of which can have multiple open goals
          val children = applyRules(rules)(goal, stats, config, ind)
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
                                                       ind: Int): Seq[Subderivation] = rules match {
      case Nil => Vector() // No more rules to apply: done expanding the goal
      case r :: rs =>
        val goalStr = s"$r: "
        // Invoke the rule
        val allChildren = r(goal)
        // Filter out out-of-order children (if commute optimization is enabled)

        // Filter out subderivations that violate rule ordering
        def goalInOrder(g: Goal): Boolean = {
          g.deriv.outOfOrder(allRules(goal)) match {
            case None => true
            case Some(app) =>
              //              printLog(List((g.deriv.preIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
              //              printLog(List((g.deriv.postIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
              printLog(List((s"$goalStr${RED}Alternative ${g.deriv.applications.head.pp} commutes with earlier ${app.pp}", BLACK)))
              false
          }
        }

        val children = if (config.commute)
          allChildren.filter(sub => sub.subgoals.forall(goalInOrder))
        else
          allChildren


        if (children.isEmpty) {
          // Rule not applicable: try other rules
          printLog(List((s"$goalStr${RED}FAIL", BLACK)), isFail = true)
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
//        // Solve all sub-goals in a sub-derivation
//        def solveSubgoals(s: Subderivation): Option[Solution] = {
//
//          // Optimization: if one of the subgoals failed, to not try the rest!
//          // <ugly-imperative-code>
//          val results = new ListBuffer[Solution]
//          import util.control.Breaks._
//          breakable {
//            for {subgoal <- s.subgoals} {
//              synthesize(subgoal, depth - 1)(stats, nextRules(subgoal, depth - 1))(ind + 1) match {
//                case Some(s) => results.append(s)
//                case _ => break
//              }
//            }
//          }
//          // </ugly-imperative-code>
//
//          if (results.size < s.subgoals.size)
//            None
//          else {
//            val (stmts, helpers) = results.unzip
//            val stmt = s.kont(stmts)
//            val allHelpers = helpers.toList.flatten
//            if (stmt.companions.contains(goal.label) && goal.label != topLabel) {
//              // Current goal is a non-top-level companion: extract a helper
//              val f = goal.toFunSpec
//              val newHelper = Procedure(f.name, f.rType, f.params, stmt)
//              Some((goal.toCall, newHelper :: allHelpers))
//            } else
//              Some((stmt, allHelpers))
//          }
//        }
//
//
  }
}