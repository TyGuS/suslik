package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

class BasicSynthesisTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  def mkSynthesiser: Synthesis = new PhasedSynthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

  describe("SL-based synthesizer") {
    runAllTestsFromDir("simple")
  }

  describe("SL-based synthesizer with entailment") {
    runAllTestsFromDir("entail")
  }

}
