package org.tygus.synsl.logic.entailment
import org.tygus.synsl.logic.{Environment, PFormula, Spec}

/**
  * @author Ilya Sergey
  */

class SimpleEntailmentSolver extends EntailmentSolver {

  val rulesToApply: List[EntailmentRule] = List(
    // TODO: Add more rules, as they are implemented
  )

  /**
    * Determines whether the spec is from the class that can be validated
    */
  def validate(spec: Spec, env: Environment): Boolean = {
    val checker = (f : PFormula) => isSimpleConjunction(isAtomicPFormula)(f)
    checker(spec.pre.phi) && checker(spec.post.phi)
  }

}
