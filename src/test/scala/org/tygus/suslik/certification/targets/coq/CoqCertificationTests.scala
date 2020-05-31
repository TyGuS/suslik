package org.tygus.suslik.certification.targets.coq

import java.io.File
import java.nio.file.{Files, Paths}

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil, defaultConfig}

import scala.sys.process._

/**
  * @author Yasunari Watanabe
  */

class CoqCertificationTests extends FunSpec with Matchers with SynthesisRunnerUtil {
  val synthesis: Synthesis = new PhasedSynthesis

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(s"certifies that it $desc") {
      val certDest = Files.createTempDirectory("suslik-").toFile
      val certDestPath = certDest.getCanonicalPath
      synthesizeFromSpec(testName, in, out, params.copy(assertSuccess = false, certTarget = Coq, certDest = certDest))
      val fname = testName.split('/').last
      val certPath = Paths.get(certDestPath, s"$fname.v").toFile.getCanonicalPath

      // verify
      val result = s"coqc -vok $certPath".!

      // check that Coq compilation succeeded
      assert(result == 0)
    }

  describe("SL-based synthesizer with certification") {
    runAllTestsFromDir("certification")
  }

}