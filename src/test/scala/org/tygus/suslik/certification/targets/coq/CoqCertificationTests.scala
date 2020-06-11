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
  val certRoot: File = Files.createTempDirectory("suslik-").toFile

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(s"certifies that it $desc") {
      synthesizeFromSpec(testName, in, out, params.copy(assertSuccess = false, certTarget = Coq, certDest = certRoot))
      val fname = testName.split('/').last
      val pathToCertificate = Paths.get(certRoot.getCanonicalPath, s"${fname.replace('-', '_')}.v").toFile.getCanonicalPath

      // verify
      val result = s"coqc -vok $pathToCertificate".!

      // check that Coq compilation succeeded
      assert(result == 0)
    }

  describe("SL-based synthesizer with certification") {
    runAllTestsFromDir("certification/ints")
    runAllTestsFromDir("certification/list")
    runAllTestsFromDir("certification/tree")
    runAllTestsFromDir("certification/sll")
  }

}