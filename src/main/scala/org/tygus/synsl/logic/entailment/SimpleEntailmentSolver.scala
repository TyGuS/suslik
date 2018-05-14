package org.tygus.synsl.logic.entailment
import org.tygus.synsl.logic.{Environment, PFormula, Goal}
import org.tygus.synsl.util.SynLogging

/**
  * @author Ilya Sergey
  */

class SimpleEntailmentSolver(override implicit val log: SynLogging) extends EntailmentSolver {

  val rulesToApply: List[EntailmentRule] = List(
    // Normalization Rules

    // TODO: add *-Partial
    // TODO: add ExcludedMiddle

    StripEqPre,
    Inconsistency,
    Substitution,

    // Subtraction Rules
    Axiom,
    StarIntro,
    Hypothesis,
    StripEqPost

  )

  /**
    * Determines whether the goal is from the class that can be validated
    */
  def validate(goal: Goal, env: Environment): Boolean = {
    val checker = (f : PFormula) => isCNF(isAtomicPFormula)(f)
    checker(goal.pre.phi) && checker(goal.post.phi)
  }

}
