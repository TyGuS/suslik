package org.tygus.synsl.entailment

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.logic.entailment.SimpleEntailmentSolver
import org.tygus.synsl.logic.{Environment, PureLogicUtils}
import org.tygus.synsl.parsing.SynslParser
import org.tygus.synsl.util.{SynLogLevels, SynLogging}

/**
  * @author Ilya Sergey
  */

class EntailmentTests extends FunSpec with Matchers with PureLogicUtils {

  val espec1 = "{(x == x) /\\ (y == x) ; emp} {true ; emp}"
  val espec2 = "{(x == x) /\\ (y == x) ; emp} { (x == x) /\\ ((y == y) /\\ true) ; emp}"
  val espec3 = "{(x == x) /\\ (y == x) ; emp} { (x == x) /\\ ((x == y) /\\ true) ; emp}"
  val espec4 = "{(x == x) /\\ (y == a) ; x :-> y ** y :-> z} " +
      "{ (x == x) /\\ ((a == y) /\\ true) ; y :-> z ** x :-> y}"
  val espec5 = "{(z == 5) /\\ (y == a)    ; x :-> y ** y :-> z} { (x == x) /\\ ((a == y) /\\ true) ; y :-> 5 ** x :-> y}".format()
  val espec6 = "{(z == y) /\\ (not (y == z))    ; x :-> y ** y :-> z} { (x == x) /\\ ((a == y) /\\ true) ; y :-> 5 ** x :-> y}".format()
  val espec7 = "{(z == 5) /\\ (x == x)    ; x :-> y ** y :-> z} { true ; y :-> 5 ** x :-> y}".format()

  implicit val log : SynLogging = SynLogLevels.Test

  private def checkEntailment(text: String) {
    val parser = new SynslParser
    val res = parser.parseSpec(text)
    assert(res.successful, res)

    val spec = res.get.simpl

    // Assert that these are conjunctions
    assert(isCNF(isAtomicPFormula)(spec.pre.phi))
    assert(isCNF(isAtomicPFormula)(spec.post.phi))

    val checker = new SimpleEntailmentSolver

    // TODO: add environments
    val env = Environment(Map.empty)
    assert(checker.entails(spec, env), s"Entailment for spec ${spec.pp} doesn't hold!")
  }

  ///////////////////////////////////////////////////////////////////////////

  describe("Simple entailment checker") {
    it("should be able to check trivial entailment with emp") {
      // Testing [Axiom]
      checkEntailment(espec1)
    }

    it("should be able to discharge trivial equalities in the postcondition") {
      // Testing [=-R]
      checkEntailment(espec2)
    }

    it("should be able to remove duplicating hypotheses") {
      // Testing [Hypothesis]
      checkEntailment(espec3)
    }

    it("should be able to prove heap entailment by subtracting heaplets") {
      // Testing [*-Introduction]
      checkEntailment(espec4)
    }

    it("should be able to substitute equalities") {
      // Testing [Substitution]
      checkEntailment(espec5)
    }

    it("should be able to use the inconsistencies") {
      // Testing [Inconsistency]
      checkEntailment(espec6)
    }

    it("should be able to discharge trivial equalities in the precondition") {
      // Testing [=-L]
      checkEntailment(espec7)
    }

  }

}
