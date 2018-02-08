package org.tygus.synsl

import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic.Specifications._

/**
  * @author Ilya Sergey
  */

object Synthesis extends Rules {

  val defaultName = "foo"
  val rulesToApply: List[Rule] = List(EmpRule, FrameRule, ReadRule, WriteRule, FreeRule, AllocRule)
  val maxDepth = 25


  def synthesizeProc(fullSpec: FullSpec): Option[Procedure] = {
    val FullSpec(spec, tp, name) = fullSpec
    synthesize(spec, 0) match {
      case Some(body) => Some(Procedure(name.getOrElse(defaultName), tp, spec.gamma, body))
      case None =>
        println(s"Deductive synthesis failed for the spec\n ${spec.pp},\n depth = $maxDepth.")
        None
    }

  }

  private def synthesize(spec: Spec, depth: Int): Option[Statement] = {

    if (depth > maxDepth) return None

    def tryRules(rules: List[Rule]): Option[Statement] = rules match {
      case Nil => None
      case r :: rs =>
        val result: RuleResult = r(spec)
        print(s"Trying rule $r for spec ${spec.pp}: ")
        result match {
          case Fail() =>
            println(s"FAIL\n")
            tryRules(rs) // rule not applicable: try the rest
          case MoreGoals(goals, kont) =>
            println(s"SUCCESS${goals.map(g => s"\n\t${g.pp}").mkString}\n")
            // Synthesize subgoals
            val subGoalResults = (for (subgoal <- goals) yield synthesize(subgoal, depth + 1)).toStream
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
