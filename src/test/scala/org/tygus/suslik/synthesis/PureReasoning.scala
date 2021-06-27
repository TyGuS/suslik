package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Ilya Sergey
  */

class PureReasoning extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("SL-based synthesizer with theory of integers") {
    runAllTestsFromDir("ints")
  }

  describe("SL-based synthesizer with theory of finite sets") {
    runAllTestsFromDir("sets")
  }

  describe("Stuff that didn't work at some point") {
    runAllTestsFromDir("regression")
  }

}
