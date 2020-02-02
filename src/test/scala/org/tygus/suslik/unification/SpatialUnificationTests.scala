package org.tygus.suslik.unification

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.logic.PureLogicUtils
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic.unification.SpatialUnification
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.util.SynLogLevels

class SpatialUnificationTests extends FunSpec with Matchers with PureLogicUtils {

  type UGoal = (Assertion, Set[Var])

  private def getSourceTarget(sourceText: String, targetText: String): (UGoal, UGoal) = {
    val parser = new SSLParser
    val targetRes = parser.parseUnificationGoal(targetText)
    val sourceRes = parser.parseUnificationGoal(sourceText)
    assert(targetRes.successful, targetRes)
    assert(sourceRes.successful, sourceRes)

    val target = targetRes.get
    val source = sourceRes.get
    (target, source)
  }

  val log = SynLogLevels.Test

  import log._

  /** ****************************************************
    * Success tests
    * ***************************************************/

  val uSource1 = "(a) {(a == a) /\\ (b == b); a :-> b}"
  val uTarget1 = "(x) {true ; x :-> y}"

  val uSource2 = "(y) {(y == y) /\\ (x == x); y :-> x}"
  val uTarget2 = "(x) {true ; x :-> y}"

  val uSource3 = "(a, b) {true ; a :-> b ** [b, 1] ** b :-> c}"
  val uTarget3 = "(y, x) {true ; y :-> z ** x :-> y ** [y, 1]}"

  val uSource4 = "(a) {true ; a :-> b ** [b, 1] ** b :-> c}"
  val uTarget4 = "(y, x) {true ; y :-> y ** x :-> y ** [y, 1]}"

  val uSource5 = "(r) {true ; r :-> c ** c :-> a ** lseg(a, r)}"
  val uTarget5 = "(y, x) {true ; lseg(y, x) ** x :-> z ** z :-> y}"

  val uSource6 = "(r) {lseg(r) ** x :-> a ** a :-> r}"
  val uTarget6 = "(y) {lseg(y) ** x :-> z ** z :-> y}"

  //////////////////////////////////////////////////

  private def checkUnificationSuccess(sourceText: String, targetText: String,
                                      global: Set[String] = Set.empty) {
    val ((target, tParams), (source, sParams)) = getSourceTarget(sourceText, targetText)
    val globalVars = global.map(Var)

    // Assert that these are conjunctions
    SpatialUnification.unify(target, source, globalVars) match {
      case Some(sbst) =>
        val res = source.subst(sbst)
        testPrintln(s"Unified")
        testPrintln(s"${source.pp}", Console.BLUE)
        testPrintln("  with")
        testPrintln(s"${target.pp}", Console.BLUE)
        testPrintln("Adapted source and substitution:")
        testPrintln(s"${res.pp}", Console.BLUE)
        testPrintln(s"${SpatialUnification.ppSubst(sbst)}\n", Console.MAGENTA)
      case None =>
        assert(false, s"Failed to unify\n$source\nwith\n$target\n")
    }
  }

  describe("Unification for spatial assertions should succeed for ") {

    it("a single heaplet with non-fresh variables") {
      checkUnificationSuccess(uSource2, uTarget2)
    }

    it("a single heaplet") {
      checkUnificationSuccess(uSource1, uTarget1)
    }

    it("assertions with blocks") {
      checkUnificationSuccess(uSource3, uTarget3)
    }

    it("assertions with non-trivial existentials") {
      checkUnificationSuccess(uSource4, uTarget4)
    }

    it("assertions with predicate symbols") {
      checkUnificationSuccess(uSource5, uTarget5)
    }

    it("assertions in the presence of globally bound names") {
      checkUnificationSuccess(uSource6, uTarget6, Set("x"))
    }
    
  }


  /** ****************************************************
    * Failure tests
    * ***************************************************/

  //  Fail: to unify, "c" has to be substituted "z", but the latter is a ghost in the target
  val uSource1_fail = "(r, c) {true ; r :-> c ** c :-> a ** lseg(a, r)}"
  val uTarget1_fail = "(y, x) {true ; lseg(y, x) ** x :-> z ** z :-> y}"

  //  Fail: cannot unify the heapler
  val uSource2_fail = "(r) {true ; r :-> r}"
  val uTarget2_fail = "(x, y) {true ; x :-> y}"

  //  Fail if x is globally bound
  val uSource3_fail = "(r) {lseg(r) ** x :-> a ** a :-> r}"
  val uTarget3_fail = "(y) {lseg(y) ** y :-> z ** z :-> y}"


  //  Fail: cannot with unaccounted parameters
  val uSource4_fail = "(r, c) {r == c; r :-> r}"
  val uTarget4_fail = "(x, y) {true ; x :-> x}"


  /////////////////////////////////////////////////////////////////////

  private def checkUnificationFailure(sourceText: String, targetText: String,
                                      global: Set[String] = Set.empty) {
    val ((target, tParams), (source, sParams)) = getSourceTarget(sourceText, targetText)
    val globalVars = global.map(Var)

    // Assert that these are conjunctions
    SpatialUnification.unify(target, source, globalVars) match {
      case Some(sbst) =>
        val res = source.subst(sbst)
        // Now need to check the ghost flow
        if (SpatialUnification.checkGhostFlow(sbst, target, tParams, source, sParams)) {
          testPrintln(s"Weird! Unified\nSource ${source.pp}\nwith\nTarget ${target.pp}\n" +
            s"Adapted source:\n${res.pp}\nSubstitution (source -> target):\n${SpatialUnification.ppSubst(sbst)}\n")
          assert(false, "Unification shouldn't succeed")
        } else {
          // Good!
        }
      case None =>
        testPrintln(s"As expected, failed to unify")
        testPrintln(s"${source.pp}", Console.BLUE)
        testPrintln("  with")
        testPrintln(s"${target.pp}\n", Console.BLUE)
    }
  }

  describe("Unification for spatial assertions should fail when ") {
    
    it("trying to install ghosts for parameters") {
      checkUnificationFailure(uSource1_fail, uTarget1_fail)
    }

    it("trying to unify incompatible points-to assertions") {
      checkUnificationFailure(uSource2_fail, uTarget2_fail)
    }

    it("trying to unify assertions with globally bound names") {
      checkUnificationFailure(uSource3_fail, uTarget3_fail, Set("x"))
    }

  }

}
