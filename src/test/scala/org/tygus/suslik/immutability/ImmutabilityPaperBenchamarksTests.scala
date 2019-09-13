package org.tygus.suslik.immutability

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil, defaultConfig}

/**
  * @author Ilya Sergey
  */
class ImmutabilityPaperBenchamarksTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  val synthesis: Synthesis = new PhasedSynthesis


  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

//  keep only those categories which are already annotated with imm

//  describe("bst") {
//    runAllTestsFromDir("../immutable-synthesis/regression/paper-benchmarks/old/bst")
//  }

  describe("ints") {
    // NOTHING iSPECIAL WITH THIS BENCHMARK
    runAllTestsFromDir("../immutable-synthesis/regression/paper-benchmarks/old/ints")
  }

  describe("sll") {
    runAllTestsFromDir("../immutable-synthesis/regression/paper-benchmarks/old/sll")
  }

  describe("sll-bounds") {
    runAllTestsFromDir("../immutable-synthesis/regression/paper-benchmarks/old/sll-bounds")
  }

  describe("srtl") {
    runAllTestsFromDir("../immutable-synthesis/regression/paper-benchmarks/old/srtl")
  }

  describe("tree") {
    runAllTestsFromDir("../immutable-synthesis/regression/paper-benchmarks/old/tree")
  }

}
