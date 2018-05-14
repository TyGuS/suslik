package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.synthesis.instances.SimpleSynthesis

/**
  * @author Ilya Sergey
  */

class LinkedListTests extends FunSpec with Matchers with SynthesisTestUtil {

  val synthesis: Synthesis = new SimpleSynthesis

  def doTest(testName: String, desc: String, in: String, out: String, params: TestParams = defaultTestParams): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("SL-based synthesizer with linked lists") {
    runAllTestsFromDir("llist")
  }

}
