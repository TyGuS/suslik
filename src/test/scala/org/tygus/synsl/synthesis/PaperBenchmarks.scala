package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.synthesis.instances.PhasedSynthesis

class PaperBenchmarks extends FunSpec with Matchers with SynthesisTestUtil {

  val synthesis: Synthesis = new PhasedSynthesis

  def doTest(testName: String, desc: String, in: String, out: String, params: TestParams = defaultTestParams): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("SuSLik should be able synthesize") {
    runAllTestsFromDir("paper-examples")
  }

  describe("Benchmarks from Natural Synthesis paper") {
    runAllTestsFromDir("paper-benchmarks/natural")
  }

  describe("Benchmarks from Dryad suite") {
    runAllTestsFromDir("paper-benchmarks/dryad")
  }


}