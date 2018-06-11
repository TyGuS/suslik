package org.tygus.synsl.unification

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.logic.unification.{SpatialUnification, UnificationGoal}
import org.tygus.synsl.logic.PureLogicUtils
import org.tygus.synsl.parsing.SynslParser
import org.tygus.synsl.util.SynLogLevels

class SpatialUnificationTests extends FunSpec with Matchers with PureLogicUtils {

  private def getSourceTarget(sourceText: String, targetText: String) = {
    val parser = new SynslParser
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

  //////////////////////////////////////////////////

  private def checkUnificationSuccess(sourceText: String, targetText: String) {
    val (target: UnificationGoal, source: UnificationGoal) = getSourceTarget(sourceText, targetText)

    // Assert that these are conjunctions
    SpatialUnification.unify(target, source, precise = false) match {
      case Some(sbst) =>
        val res = source.formula.subst(sbst)
        testPrintln(s"Unified")
        testPrintln(s"$source", Console.BLUE)
        testPrintln("  with")
        testPrintln(s"$target", Console.BLUE)
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
  }


  /** ****************************************************
    * Failuretests
    * ***************************************************/

  //  Fail: to unify, "c" has to be substituted "z", but the latter is a ghost in the target
  val uSource1_fail = "(r, c) {true ; r :-> c ** c :-> a ** lseg(a, r)}"
  val uTarget1_fail = "(y, x) {true ; lseg(y, x) ** x :-> z ** z :-> y}"

  //  Fail: cannot unify the heapler
  val uSource2_fail = "(r) {true ; r :-> r}"
  val uTarget2_fail = "(x, y) {true ; x :-> y}"

  //  Fail: cannot with unaccounted parameters
  val uSource3_fail = "(r, c) {r == c; r :-> r}"
  val uTarget3_fail = "(x, y) {true ; x :-> x}"

  /////////////////////////////////////////////////////////////////////

  private def checkUnificationFailure(sourceText: String, targetText: String) {
    val (target: UnificationGoal, source: UnificationGoal) = getSourceTarget(sourceText, targetText)

    // Assert that these are conjunctions
    SpatialUnification.unify(target, source) match {
      case Some(sbst) =>
        val res = source.formula.subst(sbst)
        testPrintln(s"Weird! Unified\nSource $source\nwith\nTarget $target\n" +
            s"Adapted source:\n${res.pp}\nSubstitution (source -> target):\n${SpatialUnification.ppSubst(sbst)}\n")
        assert(false, "Unification shouldn't succeed")
      case None =>
        testPrintln(s"As expected, failed to unify")
        testPrintln(s"$source", Console.BLUE)
        testPrintln("  with")
        testPrintln(s"$target\n", Console.BLUE)
    }
  }

  describe("Unification for spatial assertions should fail when ") {
    it("trying to install ghosts for parameters") {
      checkUnificationFailure(uSource1_fail, uTarget1_fail)
    }

    it("trying to unify incompatible points-to assertions") {
      checkUnificationFailure(uSource2_fail, uTarget2_fail)
    }

    //    it("trying to unify assertions with unaccounted variables") {
    //      checkUnificationFailure(uSource3_fail, uTarget3_fail)
    //    }
  }

}
