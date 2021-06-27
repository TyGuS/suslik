package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Ilya Sergey
  */

class LinkedStructuresTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("Packed binary trees") {
    runAllTestsFromDir("packed")
  }


  describe("SL-based synthesizer with linked lists") {
    runAllTestsFromDir("llist")
  }

  describe("SL-based synthesizer for doubly-linked lists") {
    runAllTestsFromDir("dllist")
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

  describe("SL-based synthesizer with mutable trees") {
    runAllTestsFromDir("tree")
  }


}
