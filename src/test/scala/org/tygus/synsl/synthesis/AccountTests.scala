package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.synthesis.instances.PhasedSynthesis

/**
  * @author Ilya Sergey
  */

class AccountTests extends FunSpec with Matchers with SynthesisTestUtil {

  val synthesis: Synthesis = new PhasedSynthesis

  def doTest(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultTestParams): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("SL-based synthesizer with one-constructor predicates") {
    runAllTestsFromDir("account")
  }

}