package org.tygus.synsl.logic.entailment
import org.tygus.synsl.logic.{Environment, PFormula, Spec}
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
    * Determines whether the spec is from the class that can be validated
    */
  def validate(spec: Spec, env: Environment): Boolean = {
    val checker = (f : PFormula) => isCNF(isAtomicPFormula)(f)
    checker(spec.pre.phi) && checker(spec.post.phi)
  }

}
