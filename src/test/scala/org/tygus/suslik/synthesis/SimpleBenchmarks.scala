package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

class SimpleBenchmarks extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("Integers") {
    runAllTestsFromDir("simple-benchmarks/ints")
  }

  describe("Singly-linked list with bounds") {
    runAllTestsFromDir("simple-benchmarks/sll-bounds")
  }

  describe("Singly-linked list with set of elements") {
    runAllTestsFromDir("simple-benchmarks/sll")
  }

  describe("Sorted list") {
    runAllTestsFromDir("simple-benchmarks/srtl")
  }

  describe("Trees with size or elements") {
    runAllTestsFromDir("simple-benchmarks/tree")
  }

  describe("Binary search trees") {
    runAllTestsFromDir("simple-benchmarks/bst")
  }

  describe("Doubly-linked list with set of elements") {
    runAllTestsFromDir("simple-benchmarks/dll")
  }

}
