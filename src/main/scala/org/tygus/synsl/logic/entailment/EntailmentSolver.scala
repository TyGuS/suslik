package org.tygus.synsl.logic.entailment

import org.tygus.synsl.logic._
import org.tygus.synsl.util.SynLogging

abstract class EntailmentSolver(implicit val log: SynLogging) extends EntailmentRules {

  val rulesToApply: List[EntailmentRule]

  import log._

  /**
    * Determines whether the spec is from the class that can be validated
    */
  def validate(spec: Spec, env: Environment) : Boolean

  def entails(spec: Spec, env: Environment): Boolean = {
    if (!validate(spec, env)) {
      printlnErr(s"Cannot validate the spec: $spec in the environment $env.")
      return false
    }

    def tryRules(rules: List[EntailmentRule]): Boolean = rules match {
      case Nil => false
      case r :: rs =>
        val result = r(spec, env)
        print(s"[Entl] Trying entailment rule $r for ${spec.pp}: ")
        result match {
          case EntFail =>
            println(s"\nFAIL\n")
            tryRules(rs) // rule not applicable: try the rest
          case EntMoreGoals(goals) =>
            println(s"\nSUCCESS\n${goals.map(g => s"New goal: ${g.pp}\n").mkString}")
            // Proceed with сруслштп subgoals
            val subGoalResults = goals.toStream.forall(subgoal => entails(subgoal, env))
            if (!subGoalResults) {
              // Some of the subgoals have failed: backtrack
              tryRules(rs)
            } else {
              true
            }

        }
    }
    tryRules(rulesToApply)
  }

}
