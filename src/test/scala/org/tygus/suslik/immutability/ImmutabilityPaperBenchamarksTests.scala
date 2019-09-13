package org.tygus.suslik.immutability

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil, defaultConfig}

/**
  * @author Ilya Sergey
  */
class ImmutabilityPaperBenchamarksTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  val synthesis: Synthesis = new PhasedSynthesis
  val PATH: String = "../immutable-synthesis/paper-benchmarks/"


  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

  // ***********************************************************
  // LL: the predicate definitions includes linked list definition
  // ***********************************************************

  describe("bst") {
    runAllTestsFromDir(PATH + "old/ll/bst")
  }

  describe("ints") {
    // NOTHING iSPECIAL WITH THIS BENCHMARK
    runAllTestsFromDir(PATH + "old/ll/ints")
  }

  describe("sll") {
    runAllTestsFromDir(PATH + "old/ll/sll")
  }

  describe("sll-bounds") {
    runAllTestsFromDir(PATH + "old/ll/sll-bounds")
  }

  describe("srtl") {
    runAllTestsFromDir(PATH + "old/ll/srtl")
  }

  describe("tree") {
    runAllTestsFromDir(PATH + "old/ll/tree")
  }

  // ***********************************************************
  // LSEG: the predicate definitions includes linked list segments
  // ***********************************************************


    describe("bst") {
      runAllTestsFromDir(PATH + "old/ll/bst")
    }

  describe("ints") {
    // NOTHING iSPECIAL WITH THIS BENCHMARK
    runAllTestsFromDir(PATH + "old/lseg/ints")
  }

  describe("sll") {
    runAllTestsFromDir(PATH + "old/lseg/sll")
  }

  describe("sll-bounds") {
    runAllTestsFromDir(PATH + "old/lseg/sll-bounds")
  }

  describe("srtl") {
    runAllTestsFromDir(PATH + "old/lseg/srtl")
  }

  describe("tree") {
    runAllTestsFromDir(PATH + "old/lseg/tree")
  }

}
