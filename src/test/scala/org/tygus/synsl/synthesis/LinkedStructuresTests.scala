package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.synthesis.instances.PhasedSynthesis

/**
  * @author Ilya Sergey
  */

class LinkedStructuresTests extends FunSpec with Matchers with SynthesisTestUtil {

  val synthesis: Synthesis = new PhasedSynthesis

  def doTest(testName: String, desc: String, in: String, out: String, params: TestParams = defaultTestParams): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("SL-based synthesizer with linked lists") {
    runAllTestsFromDir("llist")
  }

  describe("SL-based synthesizer with mutable trees") {
    runAllTestsFromDir("tree")
  }

  describe("SL-based synthesizer for linked lists parametrized by length") {
    runAllTestsFromDir("copy-len")
  }

  describe("SL-based synthesizer for linked lists parametrized by set of elements") {
    runAllTestsFromDir("copy")
  }

  describe("SL-based synthesizer for collections set of elements") {
    runAllTestsFromDir("flatten")
  }

  describe("SL-based synthesizer for doubly-linked lists") {
    runAllTestsFromDir("dllist")
  }

}
