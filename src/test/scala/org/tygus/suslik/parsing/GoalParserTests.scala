package org.tygus.suslik.parsing

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.util.SynLogLevels

/**
  * @author Ilya Sergey
  */

class GoalParserTests extends FunSpec with Matchers {

  val spec1 = "{true; emp} void foo(int x) {true ; emp}"
  val spec2 = "{true; emp} void foo(int x, bool y, int z) {true ; emp}"
  val spec3 = "{true; x :-> a} void foo(int x, bool y, int z) {true ; x :-> 42}"
  val spec4 = "{true; x :-> a ** y :-> b} void swap(int x, bool y) {true ; y :-> a ** x :-> b}"
  val spec5 = "{true; x :-> 41 } void swap(int x, bool y) {42 < a ; y :-> a}"
  val spec6 = "{true; x :-> 41 } void swap(int x, bool y) {(42 < a) /\\ (a < 40) ; y :-> a}"
  val spec7 = "{(42 < b) \\/ (b < 40); x :-> b } void swap(int x, bool y) {(42 < a) /\\ (a < 40) ; y :-> a}"
  val spec8 = "{true; x :-> a ** x + 1 :-> b} void swap(loc x, loc y) {true ; x :-> b ** (x + 1) :-> a}"
  val spec9 = "{true; [x, 2] ** x :-> a ** x + 1 :-> b} void delete(loc x) {true ; emp}"
  val spec10 = "{[x..y] == []; emp} void interval_test(int x, int y) {[x..y] == [x]; emp}"
  val spec11 = "{emp} void interval_test(int x, int y) {lower [x..y] == lower [x] && upper [x..y] == upper [y]; emp}"

  val log = SynLogLevels.Test
  import log._

  def parseSimpleSpec(text: String) {
    val parser = new SSLParser
    val result = parser.parseGoal(text)
    // So far, just assert that the result is a success
    assert(result.successful, result)
    println(result.get.pp)
  }

  describe("Parser for SSL specs") {
    it("should parse simple specifications with one parameter") {
      parseSimpleSpec(spec1)
    }

    it("should parse simple specifications with multiple parameters") {
      parseSimpleSpec(spec2)
    }

    it("should parse points-to assertions") {
      parseSimpleSpec(spec3)
    }

    it("should parse complex heaps") {
      parseSimpleSpec(spec4)
    }

    it("should parse simple pure formulas") {
      parseSimpleSpec(spec5)
    }

    it("should parse complex pure formulas - 1") {
      parseSimpleSpec(spec6)
    }

    it("should parse complex pure formulas - 2") {
      parseSimpleSpec(spec7)
    }

    it("should parse pointer offsets") {
      parseSimpleSpec(spec8)
    }

    it("should parse malloc blocks") {
      parseSimpleSpec(spec9)
    }

    it("should parse interval literals") {
      parseSimpleSpec(spec10)
    }

    it("should parse interval bounds") {
      parseSimpleSpec(spec11)
    }
  }


}
