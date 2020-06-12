package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

class CyclicTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("Synthesis with cyclic proofs") {
    runAllTestsFromDir("cyclic")
  }

  describe("Mutual recursion") {
    runAllTestsFromDir("mutual")
  }

}
