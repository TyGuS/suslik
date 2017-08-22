package org.tygus.synsl.parsing

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Ilya Sergey
  */

class SpecParserTests extends FunSpec with Matchers {

  val spec1 = "{true; emp} void foo(int x) {true ; emp}"
  val spec2 = "{true; emp} void foo(int x, bool y, int z) {true ; emp}"
  val spec3 = "{true; x :-> a} void foo(int x, bool y, int z) {true ; x :-> 42}"
  val spec4 = "{true; x :-> a ** y :-> b} void swap(int x, bool y) {true ; y :-> a ** x :-> b}"
  val spec5 = "{true; x :-> 41 } void swap(int x, bool y) {42 < a ; y :-> a}"
  val spec6 = "{true; x :-> 41 } void swap(int x, bool y) {(42 < a) /\\ (a < 40) ; y :-> a}"
  val spec7 = "{(42 < b) \\/ (b < 40); x :-> b } void swap(int x, bool y) {(42 < a) /\\ (a < 40) ; y :-> a}"



  def parseSimpleSpec(text: String) {
    val parser = new SynslParser
    val result = parser.parse(text)
    // So far, just assert that the result is a success
    assert(result.successful, result)
    println(result.get.pp)
  }

  describe("Parser for SynSL specs") {
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
  }


}
