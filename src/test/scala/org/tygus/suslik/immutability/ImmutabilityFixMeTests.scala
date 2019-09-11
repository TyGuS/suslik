package org.tygus.suslik.immutability

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil, defaultConfig}

class ImmutabilityFixMeTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  val synthesis: Synthesis = new PhasedSynthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

  describe("failing-examples") {
    runAllTestsFromDir("../immutable-synthesis/fixme/failing-examples")
  }

  describe("flatten") {
    runAllTestsFromDir("../immutable-synthesis/fixme/flatten")
  }

  describe("questionable") {
    runAllTestsFromDir("../immutable-synthesis/fixme/questionable")
  }

  describe("tree") {
    runAllTestsFromDir("../immutable-synthesis/fixme/tree")
  }

}
