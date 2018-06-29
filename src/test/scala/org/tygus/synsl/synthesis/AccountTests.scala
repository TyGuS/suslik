package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Ilya Sergey
  */

class AccountTests extends FunSpec with Matchers with SynthesisTestUtil {

  def doTest(testName: String, desc: String, in: String, out: String, params: TestParams = defaultTestParams): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("SL-based synthesizer with one-constructor predicates") {
    runAllTestsFromDir("account")
  }

}