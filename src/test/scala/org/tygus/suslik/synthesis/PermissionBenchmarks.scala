package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

class PermissionBenchmarks extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("Single-Linked Lists") {
    runAllTestsFromDir("permissions/sll")
  }

  describe("Sorted lists") {
    runAllTestsFromDir("permissions/srtl")
  }

  describe("Doubly-linked lists") {
    runAllTestsFromDir("permissions/dll")
  }

  describe("Lists of lists") {
    runAllTestsFromDir("permissions/multi-list")
  }

  describe("Trees") {
    runAllTestsFromDir("permissions/tree")
  }

  describe("Rose tree") {
    runAllTestsFromDir("permissions/rose-tree")
  }

//  describe("Binary search tree") {
//    runAllTestsFromDir("permissions/bst")
//  }
//
//  describe("Packed tree") {
//    runAllTestsFromDir("permissions/packed")
//  }
}
