package org.tygus.suslik.fixme

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis._

/**
  * @author Roman Shchedrin
  */

// TODO [holes]: remove `abstract` modifier when fixed
abstract class HolesTests extends FunSpec with Matchers with SynthesisRunnerUtil  {

  def isNegative(out: String): Boolean = {
    out == "ERROR"
  }

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    if (isNegative(out)) {
      // If this is a negative test, make sure it throws a synthesis exception
      it(desc) {
        val err = intercept[Exception](synthesizeFromSpec(testName, in, out, params))
        // Can be either a memory error, or a failed entailment proof, which manifests as synthesis exception:
        assert(err.isInstanceOf[SymbolicExecutionError] || err.isInstanceOf[SynthesisException])
      }
    } else {
      // Otherwise, make sure it succeeds and produces the right results
      it(desc) {
        synthesizeFromSpec(testName, in, out, params)
      }
    }
  }

  describe("Holes tests") {
    runAllTestsFromDir("holes")
  }

}
