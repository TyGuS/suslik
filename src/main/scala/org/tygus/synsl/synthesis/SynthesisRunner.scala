package org.tygus.synsl.synthesis

import org.tygus.synsl.synthesis.instances.PhasedSynthesis
import org.tygus.synsl.util.{SynLogLevels, SynLogging}

/**
  * @author Ilya Sergey
  */

object SynthesisRunner extends SynthesisTestUtil {

  // Enable verbose logging
  override implicit val log: SynLogging = SynLogLevels.Verbose

  import log._

  val synthesis: Synthesis = new PhasedSynthesis

  /**
    * Running a single test file (2nd argument) from a folder (1 argument) under
    * ./src/test/resources/synthesis
    *
    * For instance, you can run from IntelliJ config by passing, e.g.,
    * simple emp
    * as program arguments
    *
    * You can also do it using sbt from the command line (from the project root):
    *
    * sbt "test:runMain org.tygus.synsl.synthesis.SynthesisTestRunner paper-examples 01-swap"
    *
    */
  def main(args: Array[String]): Unit = handleInput(args)

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig): Unit = {
    println(desc)
    println()
    synthesizeFromSpec(testName, in, out, params)
  }

  case class RunConfig(synConfig: SynConfig, dirName: String, fileName: String)

  val TOOLNAME = "SuSLik"
  val SCRIPTNAME = "suslik"
  private val VERSION = "0.1"
  private val VERSION_STRING = s"v$VERSION"

  private val defaultFolder = "paper-examples"
  private val defaultFile = "01-swap"

  private def handleInput(args: Array[String]): Unit = {
    val newConfig = RunConfig(SynConfig(), defaultFolder, defaultFile)
    parser.parse(args, newConfig) match {
      case Some(RunConfig(synConfig, dir, file)) =>
        runSingleTestFromDir(dir, file, synConfig)
      case None =>
        System.err.println("Bad argument format.")
    }
  }

  private val parser = new {

  } with scopt.OptionParser[RunConfig](SCRIPTNAME) {
    // See examples at https://github.com/scopt/scopt

    head(TOOLNAME, VERSION_STRING)

    arg[String]("folder").action {(x, c) =>
      c.copy(dirName = x)
    }.text("a folder under ./src/test/resources/synthesis starting from this on as a root")

    arg[String]("file").action {(x, c) =>
      c.copy(fileName = x)
    }.text("a test case file under the specified folder")

    opt[Boolean]('t', "trace").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printDerivations = b))
    }.text("print the entire derivation trace; default: true")

    opt[Boolean]('a', "assert").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(assertSuccess = b))
    }.text("check that the synthesized result matches the last part of the test file; default: false")

    help("help").text("prints this usage text")

    note("\nOnce the synthesis is done execution statistics will be available in stats.csv.\n")

  }
}
