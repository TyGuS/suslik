package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Abhishek Sharma, Aidan Denlinger
  */

class SequencesTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("Pure synthesis with sequences") {
    runAllTestsFromDir("sequences/pure")
  }

  describe("Linked lists with sequences") {
    runAllTestsFromDir("sequences/llist")
  }

  describe("Doubly-linked list with sequence of elements") {
    runAllTestsFromDir("sequences/paper-benchmarks/dll")
  }

  describe("Singly-linked list with sequence of elements") {
    runAllTestsFromDir("sequences/paper-benchmarks/sll")
  }

}