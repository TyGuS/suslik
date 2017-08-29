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
        // println(s"Rule $r is ${if (r.isApplicable(spec)) "" else "NOT"} applicable for spec ${spec.pp}\n")


        if (!r.isApplicable(spec)) tryRules(rs)
        else {
          // rule is applicable
          val result: RuleResult = r(spec)
          result match {
            case LastStatement(st) => Some(st)
            case MoreGoals(goals, kont) =>
              // Synthesize the rest lazily
              val stmts = (for (subgoal <- goals) yield synthesize(subgoal, depth + 1)).toStream
              // Some of sub-goals have failed
              if (stmts.exists(_.isEmpty)) {
                // That was a bad rule, backtrack and try the rest of the rules
                tryRules(rs)
              } else {
                val subGoalResults = stmts.map(_.get)
                val withKont = kont(subGoalResults)
                Some(withKont)
              }

          }
        }
      case Nil => None
    }
    tryRules(rulesToApply)
  }

}
