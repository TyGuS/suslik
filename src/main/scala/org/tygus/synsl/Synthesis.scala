package org.tygus.synsl

import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic.Specifications._

/**
  * @author Ilya Sergey
  */

object Synthesis extends Rules {

  val defaultName = "foo"
  val rulesToApply: List[Rule] = List(EmpRule, FrameRule, ReadRule, WriteRule)
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
      case r :: rs =>
        if (!r.isApplicable(spec)) tryRules(rs)
        else r(spec) match {
          case LastStatement(st) => Some(st)
          case MoreGoals(goals, kont) =>
            // Synthesize the rest lazily
            val stmts = (for (subgoal <- goals) yield synthesize(subgoal, depth + 1)).toStream
            // Some of subgoals have failed
            if (stmts.exists(_.isEmpty)) None
            else {
              val subGoalResults = stmts.map(_.get)
              val withKont = kont(subGoalResults)
              Some(withKont)
            }

        }
      case Nil => None
    }
    tryRules(rulesToApply)
  }

}
