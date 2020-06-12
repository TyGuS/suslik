package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Ilya Sergey
  */

class AccountTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("SL-based synthesizer with one-constructor predicates") {
    runAllTestsFromDir("account")
  }

}