package org.tygus.synsl.synthesis

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis.rules.InvertibleRule
import org.tygus.synsl.util.SynLogging

import scala.Console.{BLUE, CYAN, GREEN, RED, BLACK, MAGENTA, YELLOW}

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis {

  val log: SynLogging

  import log._

  val synQualifier: String = "synthesis"

  case class SynthesisException(msg: String) extends SynSLException(synQualifier, msg)

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  val rulesToApply: List[SynthesisRule]
  val maxDepth: Int

  def synthesizeProc(funGoal: FunSpec, env: Environment, _printFails: Boolean = true): Option[Procedure] = {
    val FunSpec(name, tp, formals, pre, post) = funGoal
    val goal = Goal(pre, post, formals)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))(0)
    synthesize(goal, env, maxDepth)(printFails = _printFails) match {
      case Some(body) => Some(Procedure(name, tp, goal.gamma, body))
      case None =>
        printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp},\n depth = $maxDepth.")
        None
    }

  }

  private def synthesize(goal: Goal, env: Environment, maxDepth: Int = 25)
                        (implicit ind: Int = 0, printFails: Boolean): Option[Statement] = {

    if (maxDepth < 0) return None

    def tryRules(rules: List[SynthesisRule]): Option[Statement] = rules match {
      case Nil => None
      case r :: rs =>
        val result: SynthesisRuleResult = r(goal, env)
        val goalStr = s"$r: "
        result match {
          case SynFail =>
            printLog(List((s"$goalStr${RED}FAIL", BLACK)), isFail = true)
            tryRules(rs) // rule not applicable: try the rest
          case SynAndGoals(goals, kont) =>
            val succ = s"SUCCESS at depth $ind, ${goals.size} AND-goal(s):"
            val gls = s"${goals.map(g => g.pp).mkString("\n")}"
            printLog(List((s"$goalStr${GREEN}$succ", BLACK), (gls, BLUE)))
            // Synthesize subgoals
            val subGoalResults = (for (subgoal <- goals)
              yield synthesize(subgoal, env, maxDepth - 1)(ind + 1, printFails)).toStream
            if (subGoalResults.exists(_.isEmpty)) {
              // Some of the subgoals have failed
              if (r.isInstanceOf[InvertibleRule]) {
                // Inversible rule couldn't be the problem, do not try other rules
                printLog(List((s"No need to keep trying after ${r.toString}'s sub-goals have failed, return.", MAGENTA)))
                None
              } else {
                // Try other rules
                tryRules(rs)
              }
            } else {
              // All sub-goals succeeded: assemble the statement
              val stmts = subGoalResults.map(_.get)
              Some(kont(stmts))
            }
          case SynOrGoals(goals, kont) =>
            val succ = s"SUCCESS, ${goals.size} OR-goal(s)"
            printLog(List((s"$goalStr${GREEN}$succ", BLACK)))
            // Okay, I know this is ugly and the Gods of Haskell will punish me for this,
            // but breaking from loops in FP is a pain...
            val iter = goals.iterator
            var gCount = 1
            while (iter.hasNext) {
              val subgoal = iter.next()
              printLog(List((s"Trying sub-goal $gCount:", CYAN), (subgoal.pp, BLUE)))
              val res = synthesize(subgoal, env, maxDepth - 1)(ind + 1, printFails)
              if (res.nonEmpty) return Some(kont(Seq(res.get)))
              printLog(List((s"Backtracking after having tried OR-goal $gCount", YELLOW)))
              gCount = gCount + 1
            }
            tryRules(rs)
        }
    }

    tryRules(rulesToApply)
  }

  private def getIndent(implicit i: Int): String = if (i <= 0) "" else "|  " * i

  private def printLog(sc: List[(String, String)], isFail: Boolean = false)
                    (implicit i: Int, printFails: Boolean = true): Unit = {
    if (!isFail || printFails) {
      for ((s, c) <- sc if s.trim.length > 0) {
        print(s"$BLACK$getIndent")
        println(s"$c${s.replaceAll("\n", s"\n$BLACK$getIndent$c")}")
      }
    }
    print(s"$BLACK")
  }


}