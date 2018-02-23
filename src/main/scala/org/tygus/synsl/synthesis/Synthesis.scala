package org.tygus.synsl.synthesis

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis {

  val synQualifier : String = "synthesis"

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
        print(s"Trying rule $r for spec ${spec.pp}: ")
        result match {
          case SynFail =>
            println(s"[Synthesis] FAIL\n")
            tryRules(rs) // rule not applicable: try the rest
          case SynMoreGoals(goals, kont) =>
            println(s"[Synthesis] SUCCESS${goals.map(g => s"\n\t${g.pp}").mkString}\n")
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

        }
    }

    tryRules(rulesToApply)
  }

}
