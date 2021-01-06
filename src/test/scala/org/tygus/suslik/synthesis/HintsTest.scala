package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.language.Expressions.Var

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

class HintsTest extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    val hints = (List((Var("x"), 10), (Var("y"), 20)), List((Var("x"), 20), (Var("y"), 20)))
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      // hints is a pair of lists, with first element being the hints for the precondition, and second element being the hints for the postcondition
      synthesizeFromSpec(testName, in, out, params, hints)
    }
  }

  describe("SL-based synthesizer") {
    runAllTestsFromDir("hints")
  }

}
