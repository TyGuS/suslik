package org.tygus.synsl.synthesis

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis {

  val synQualifier: String = "synthesis"

  case class SynthesisException(msg: String) extends SynSLException(synQualifier, msg)

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  val rulesToApply: List[SynthesisRule]
  val maxDepth: Int

  def synthesizeProc(goal: GoalFunction, env: Environment): Option[Procedure] = {
    val GoalFunction(name, spec, tp) = goal
    synthesize(spec, env, maxDepth) match {
      case Some(body) => Some(Procedure(name, tp, spec.gamma, body))
      case None =>
        println(s"Deductive synthesis failed for the spec\n ${spec.pp},\n depth = $maxDepth.")
        None
    }

  }

  private def synthesize(spec: Spec, env: Environment, depth: Int): Option[Statement] = {

    if (depth < 0) return None

    def tryRules(rules: List[SynthesisRule]): Option[Statement] = rules match {
      case Nil => None
      case r :: rs =>
        val result: SynthesisRuleResult = r(spec, env)
        print(s"[Synt] Trying $r for spec ${spec.pp}: ")
        result match {
          case SynFail =>
            println(s"FAIL\n")
            tryRules(rs) // rule not applicable: try the rest
          case SynAndGoals(goals, kont) =>
            println(s"\nSUCCESS, ${goals.size} AND-goal(s):${goals.map(g => s"\n\t${g.pp}").mkString}\n")
            // Synthesize subgoals
            val subGoalResults = (for (subgoal <- goals) yield synthesize(subgoal, env, depth - 1)).toStream
            if (subGoalResults.exists(_.isEmpty)) {
              // Some of the subgoals have failed: backtrack
              tryRules(rs)
            } else {
              // All subgoals succeeded: assemble the statement
              val stmts = subGoalResults.map(_.get)
              Some(kont(stmts))
            }
          case SynOrGoals(goals, kont) =>
            println(s"\nSUCCESS, ${goals.size} OR-goal(s):${goals.map(g => s"\n\t${g.pp}").mkString}\n")
            // Okay, I know this is ugly and the Gods of Haskell will punish me for this,
            // but breaking from loops in FP is a pain...
            val iter = goals.iterator
            while (iter.hasNext) {
              val subgoal = iter.next()
              val res = synthesize(subgoal, env, depth - 1)
              if (res.nonEmpty) return Some(kont(Seq(res.get)))
              println(s"Backtracking after having tryed OR-goal\n\t${subgoal.pp}.\n")
            }
            tryRules(rs)
        }
    }
    tryRules(rulesToApply)
  }

}