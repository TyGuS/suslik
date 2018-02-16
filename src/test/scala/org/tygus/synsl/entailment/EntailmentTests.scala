package org.tygus.synsl.entailment

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.logic.entailment.SimpleEntailmentSolver
import org.tygus.synsl.logic.{Environment, LogicUtils}
import org.tygus.synsl.parsing.SynslParser

/**
  * @author Ilya Sergey
  */

class EntailmentTests extends FunSpec with Matchers with LogicUtils {

  val espec1 = "{(x == x) /\\ (y == x) ; emp} {true ; emp}"
  val espec2 = "{(x == x) /\\ (y == x) ; emp} { (x == x) /\\ ((y == y) /\\ true) ; emp}"
  val espec3 = "{(x == x) /\\ (y == x) ; emp} { (x == x) /\\ ((x == y) /\\ true) ; emp}"
  val espec4 = "{(x == x) /\\ (y == x) ; x :-> y ** y :-> z} " +
      "{ (x == x) /\\ ((x == y) /\\ true) ; y :-> z ** x :-> y}"

  private def checkEntailment(text: String) {
    val parser = new SynslParser
    val res = parser.parseSpec(text)
    assert(res.successful, res)

    val spec = res.get.simpl

    // Assert that these are conjunctions
    assert(isSimpleConjunction(isAtomicPFormula)(spec.pre.phi))
    assert(isSimpleConjunction(isAtomicPFormula)(spec.post.phi))

    val checker = new SimpleEntailmentSolver

    // TODO: add environments
    val env = Environment(Map.empty)
    assert(checker.entails(spec, env), s"Entailment for spec ${spec.pp} doesn't hold!")
  }

  ///////////////////////////////////////////////////////////////////////////

  describe("Simple entailment checker") {
    it("should be able to check trivial entailment with emp") {
      // Testing [emp]
      checkEntailment(espec1)
    }

    it("should be able to discharge trivial equalities") {
      // Testing [emp]
      checkEntailment(espec2)
    }

    it("should be able to remove duplicating hypotheses") {
      // Testing [emp]
      checkEntailment(espec3)
    }

    it("should be able to prove heap entailment by subtracting heaplets") {
      // Testing [emp]
      checkEntailment(espec4)
    }

  }

}
