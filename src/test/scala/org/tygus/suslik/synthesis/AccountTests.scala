package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis

/**
  * @author Ilya Sergey
  */

class AccountTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  val synthesis: Synthesis = new PhasedSynthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

  describe("SL-based synthesizer with one-constructor predicates") {
    runAllTestsFromDir("account")
  }

}