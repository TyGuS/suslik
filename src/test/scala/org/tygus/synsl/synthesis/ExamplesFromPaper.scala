package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Ilya Sergey
  */

class ExamplesFromPaper extends FunSpec with Matchers with SynthesisTestUtil {

  def doTest(testName: String, desc: String, in: String, out: String, params: TestParams = defaultTestParams): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("SuSLik should be able synthesize") {
    runAllTestsFromDir("paper-examples")
  }

}
