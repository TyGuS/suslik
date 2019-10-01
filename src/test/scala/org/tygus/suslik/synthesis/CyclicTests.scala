package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis

class CyclicTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  def mkSynthesiser: Synthesis = new PhasedSynthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

  describe("Synthesis with cyclic proofs") {
    runAllTestsFromDir("cyclic")
  }

}
