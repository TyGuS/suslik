package org.tygus.suslik.immutability

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil, defaultConfig}

/**
  * @author Ilya Sergey
  */
class ImmutabilityRegressionTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  val synthesis: Synthesis = new PhasedSynthesis


  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

  describe("basic") {
    runAllTestsFromDir("../immutable-synthesis/regression/basic")
  }

  describe("abduce") {
    runAllTestsFromDir("../immutable-synthesis/regression/abduce")
  }

  describe("copy") {
    runAllTestsFromDir("../immutable-synthesis/regression/copy")
  }

  describe("copy-len") {
    runAllTestsFromDir("../immutable-synthesis/regression/copy-len")
  }

  describe("dllist") {
    runAllTestsFromDir("../immutable-synthesis/regression/dllist")
  }

  describe("entail") {
    runAllTestsFromDir("../immutable-synthesis/regression/entail")
  }

  describe("sets") {
    runAllTestsFromDir("../immutable-synthesis/regression/sets")
  }

  describe("simple") {
    runAllTestsFromDir("../immutable-synthesis/regression/simple")
  }
  
  describe("paper-examples") {
    runAllTestsFromDir("../immutable-synthesis/regression/paper-examples")
  }

  describe("llist") {
    runAllTestsFromDir("../immutable-synthesis/regression/llist")
  }

  describe("srtl") {
    runAllTestsFromDir("../immutable-synthesis/regression/srtl")
  }
  
  describe("tree") {
    runAllTestsFromDir("../immutable-synthesis/regression/tree")
  }

}
