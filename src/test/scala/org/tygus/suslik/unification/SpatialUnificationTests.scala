package org.tygus.suslik.unification

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.language.Expressions
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic.unification.{SpatialUnification, UnificationGoal}
import org.tygus.suslik.logic.{PureLogicUtils, Specifications}
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

  //////////////////////////////////////////////////

  private def checkUnificationSuccess(sourceText: String, targetText: String) {
    val (t, s) = getSourceTarget(sourceText, targetText)

    // TODO [UGoal] remove me
    val target = UnificationGoal(t._1, t._2)
    val source = UnificationGoal(s._1, s._2)

    // Assert that these are conjunctions
    SpatialUnification.unify(target, source) match {
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
    val (t, s) = getSourceTarget(sourceText, targetText)

    // TODO [UGoal] remove me
    val target = UnificationGoal(t._1, t._2)
    val source = UnificationGoal(s._1, s._2)


    // Assert that these are conjunctions
    SpatialUnification.unify(target, source) match {
      case Some(sbst) =>
        val res = source.formula.subst(sbst)
        // Now need to check the ghost flow
        if (SpatialUnification.checkGhostFlow(sbst, t._1, t._2, s._1, s._2)) {
          testPrintln(s"Weird! Unified\nSource $source\nwith\nTarget $target\n" +
            s"Adapted source:\n${res.pp}\nSubstitution (source -> target):\n${SpatialUnification.ppSubst(sbst)}\n")
          assert(false, "Unification shouldn't succeed")
        } else {
          // Good!
        }
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
