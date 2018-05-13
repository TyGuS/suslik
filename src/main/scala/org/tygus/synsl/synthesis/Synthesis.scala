package org.tygus.synsl.synthesis

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis.rules.InvertibleRule

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis {

  val synQualifier: String = "synthesis"

  case class SynthesisException(msg: String) extends SynSLException(synQualifier, msg)

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  val rulesToApply: List[SynthesisRule]
  val maxDepth: Int

  def synthesizeProc(goal: GoalFunction, env: Environment, _printFails: Boolean = true): Option[Procedure] = {
    val GoalFunction(name, spec, tp) = goal
    synthesize(spec, env, maxDepth)(printFails = _printFails) match {
      case Some(body) => Some(Procedure(name, tp, spec.gamma, body))
      case None =>
        println(s"Deductive synthesis failed for the spec\n ${spec.pp},\n depth = $maxDepth.")
        None
    }

  }

  private def synthesize(spec: Spec, env: Environment, maxDepth: Int = 25)
                        (implicit ind: Int = 0, printFails: Boolean): Option[Statement] = {

    if (maxDepth < 0) return None
    import Console._

    def tryRules(rules: List[SynthesisRule]): Option[Statement] = rules match {
      case Nil => None
      case r :: rs =>
        val result: SynthesisRuleResult = r(spec, env)
        val goal = s"[Synt] Trying $r for spec ${spec.pp}: "
        result match {
          case SynFail =>
            printC(goal, isFail = true)
            printC(s"FAIL", RED, isFail = true)
            tryRules(rs) // rule not applicable: try the rest
          case SynAndGoals(goals, kont) =>
            printC(goal)
            printC(s"SUCCESS at depth $ind, ${goals.size} AND-goal(s):${goals.map(g => g.pp).mkString("\n")}", GREEN)
            // Synthesize subgoals
            val subGoalResults = (for (subgoal <- goals)
              yield synthesize(subgoal, env, maxDepth - 1)(ind + 1, printFails)).toStream
            if (subGoalResults.exists(_.isEmpty)) {
              // Some of the subgoals have failed: backtrack
              if (r.isInstanceOf[InvertibleRule]) {
                printC(s"FAIL (no need to backtrack)", RED, isFail = true)
                None
              } else {
                tryRules(rs)
              }
            } else {
              // All subgoals succeeded: assemble the statement
              val stmts = subGoalResults.map(_.get)
              Some(kont(stmts))
            }
          case SynOrGoals(goals, kont) =>
            printC(goal)
            printC(s"SUCCESS, ${goals.size} OR-goal(s):${goals.map(g => s"\n\t${g.pp}").mkString}", GREEN)
            // Okay, I know this is ugly and the Gods of Haskell will punish me for this,
            // but breaking from loops in FP is a pain...
            val iter = goals.iterator
            while (iter.hasNext) {
              val subgoal = iter.next()
              val res = synthesize(subgoal, env, maxDepth - 1)(ind + 1, printFails)
              if (res.nonEmpty) return Some(kont(Seq(res.get)))
              printC(s"Backtracking after having tryed OR-goal\n\t${subgoal.pp}.\n", YELLOW)
            }
            tryRules(rs)
        }
    }

    tryRules(rulesToApply)
  }

  private def getIndent(implicit i: Int): String = if (i <= 0) "" else "|  " * i

  private def printC(s: String, color: String = Console.BLACK, isFail: Boolean = false)
                    (implicit i: Int, printFails: Boolean = true): Unit = {
    if (!isFail || printFails) {
      print(s"${Console.BLACK}$getIndent")
      println(s"$color${s.replaceAll("\n", getIndent ++ "\n")}")
      print(s"${Console.BLACK}")
    }
  }


}