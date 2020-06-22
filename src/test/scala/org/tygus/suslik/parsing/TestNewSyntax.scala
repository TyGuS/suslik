package org.tygus.suslik.parsing

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.{SynConfig, SynthesisRunnerUtil, defaultConfig}


class TestNewSyntax extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }
  
  describe("New syntax test") {
    runAllTestsFromDir("syntax")
  }
}
