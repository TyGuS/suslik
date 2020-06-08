package org.tygus.suslik.certification.targets.coq

import java.io.File
import java.nio.file.{Files, Path, Paths}

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil, defaultConfig}

import scala.sys.process._

/**
  * @author Yasunari Watanabe
  */

class CoqCertificationTests extends FunSpec with Matchers with SynthesisRunnerUtil {
  val synthesis: Synthesis = new PhasedSynthesis
  val certRoot: String = Files.createTempDirectory("suslik-").toFile.getCanonicalPath
  val certLibPath: File = Files.createDirectory(Paths.get(certRoot, "lib")).toFile
  val certOutPath: File = Files.createDirectory(Paths.get(certRoot, "out")).toFile

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(s"certifies that it $desc") {
      synthesizeFromSpec(testName, in, out, params.copy(assertSuccess = false, certTarget = Coq, certDest = certOutPath))
      val fname = testName.split('/').last
      val pathToCertificate = Paths.get(certOutPath.getCanonicalPath, s"${fname.replace('-', '_')}.v").toFile.getCanonicalPath

      def copyIfMissing(filename: String): Unit = {
        val path = Paths.get(certRoot, filename)
        if (!Files.exists(path)) Files.copy(Paths.get("certification/coq", filename), path)
      }

      // compile the tactics library if needed
      if (!Files.exists(Paths.get(certRoot, "lib/core.vo"))) {
        copyIfMissing("Makefile")
        copyIfMissing("_CoqProject")
        copyIfMissing("lib/core.v")
        s"make -C $certRoot".! // compile tactics
      }

      // verify with target directory in load path
      val result = s"coqc -R $certRoot SSL -vok $pathToCertificate".!

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