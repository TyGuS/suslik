package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

class ChallengeTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("Integers") {
    runAllTestsFromDir("all-benchmarks/ints")
  }

  describe("Single-Linked Lists") {
    runAllTestsFromDir("all-benchmarks/sll")
  }

  describe("Sorted lists") {
    runAllTestsFromDir("all-benchmarks/srtl")
  }

  describe("Doubly-linked lists") {
    runAllTestsFromDir("all-benchmarks/dll")
  }

  describe("Lists of lists") {
    runAllTestsFromDir("all-benchmarks/multi-list")
  }

  describe("Trees") {
    runAllTestsFromDir("all-benchmarks/tree")
  }

  describe("Rose tree") {
    runAllTestsFromDir("all-benchmarks/rose-tree")
  }

  describe("Binary search tree") {
    runAllTestsFromDir("all-benchmarks/bst")
  }

  describe("Packed tree") {
    runAllTestsFromDir("all-benchmarks/packed")
  }
}
