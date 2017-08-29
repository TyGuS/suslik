package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.Synthesis
import org.tygus.synsl.parsing.SynslParser

/**
  * @author Ilya Sergey
  */

class SimpleSynthesisTests extends FunSpec with Matchers {

  val spec1 = "{true; emp} void foo(int x) {true ; emp}"
  val spec2 = "{true; x :-> a} void foo(int x) {true ; x :-> a}"
  val spec3 = "{true; x :-> 1} void foo(int x) {true ; x :-> 43}"
  val spec4 = "{true; x :-> 1 ** y :-> 2} void bar(int x, int y) {true ; y :-> 239 ** x :-> 43}"
  val spec5 = "{true; x :-> a ** y :-> 2} void bar(int x, int y) {true ; x :-> a ** y :-> 12}"
  val spec6 = "{true; x :-> a ** y :-> 2} void bar(int x, int y) {true ; x :-> a ** y :-> a}"
//  val spec4 = "{true; x :-> a ** y :-> b} void swap(int x, int y) {true ; x :-> b ** y :-> a}"

  import Synthesis._

  private def synthesizeFromSpec(text: String) {
    val parser = new SynslParser
    val fullSpec = parser.parse(text)
    assert(fullSpec.successful, fullSpec)

    val spec = fullSpec.get

    val sresult = synthesizeProc(spec)

    sresult match {
      case Some(res) =>
        println("Successfully synthesised:")
        println(res.pp)
      case None =>
        assert(false, s"Failed to synthesise:\n$sresult")
    }

  }

  describe("SL-based synthesizer") {
    it("should be able to synthesize an empty program") {
      // Testing [emp]
      synthesizeFromSpec(spec1)
    }

    it("should be able to synthesize an empty program with constant footprint") {
      // Testing [frame]
      synthesizeFromSpec(spec2)
    }

    it("should be able to synthesize a simple constant-assigning procedure") {
      // Testing [write]
      synthesizeFromSpec(spec3)
    }

    it("should be able to synthesize a two-pointer constant-assigning procedure") {
      // Testing [write]
      synthesizeFromSpec(spec4)
    }

    it("should be able to use [frame] and [write]") {
      // Testing [frame] and [write]
      synthesizeFromSpec(spec5)
    }

    it("should be able to synthesize a program with read") {
      // Testing [read], [frame] and [write]
      synthesizeFromSpec(spec6)
    }

//    it("should be able to synthesize a swap program") {
//      // Testing [frame]
//      synthesizeFromSpec(spec4)
//    }

  }

}
