package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}

class PaperBenchmarks extends FunSpec with Matchers with SynthesisTestUtil {

  def doTest(testName: String, desc: String, in: String, out: String, params: TestParams = defaultTestParams): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("Benchmarks from Natural Synthesis paper") {
    runAllTestsFromDir("paper-benchmarks/natural")
  }

  describe("Benchmarks from Dryad suite") {
    runAllTestsFromDir("paper-benchmarks/dryad")
  }


}
