package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.synthesis.instances.SimpleSynthesis

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

class BasicSynthesisTests extends FunSpec with Matchers with SynthesisTestUtil {

  val synthesis: Synthesis = new SimpleSynthesis

  def doTest(desc: String, in: String, out: String): Unit =
    it(desc) {
      synthesizeFromSpec(in, out)
    }

  describe("SL-based synthesizer") {
    runAllTestsFromDir("simple")
  }

  describe("SL-based synthesizer with entailment") {
    runAllTestsFromDir("entail")
  }

}
