package org.tygus.synsl.synthesis

import org.tygus.synsl.synthesis.instances.PhasedSynthesis
import org.tygus.synsl.util.{SynLogLevels, SynLogging}

/**
  * @author Ilya Sergey
  */

object SynthesisRunner extends SynthesisRunnerUtil {

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
    try {
      synthesizeFromSpec(testName, in, out, params)
    } catch {
      case SynthesisException(msg) =>
        System.err.println("Synthesis failed:")
        System.err.println(msg)
    }
  }

  case class RunConfig(synConfig: SynConfig, dirName: String, fileName: String)

  val TOOLNAME = "SuSLik"
  val SCRIPTNAME = "suslik"
  private val VERSION = "0.1"
  private val VERSION_STRING = s"v$VERSION"

  private val defaultFolder = "simple"
  private val defaultFile = "swap"

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
    }.text("a folder with the predicate definitions, lemmas, and synthesis goal file")

    arg[String]("goalName").action {(x, c) =>
      c.copy(fileName = x)
    }.text("a test case name (the file under the specified folder, called goalName.syn)")

    opt[Boolean]('r', "trace").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printDerivations = b))
    }.text("print the entire derivation trace; default: true")

    opt[Long]('t', "timeout").action { (t, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(timeOut = t))
    }.text("timeout for the derivation default (in millisecondds): 300000 (5 min)")

    opt[Boolean]('a', "assert").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(assertSuccess = b))
    }.text("check that the synthesized result matches the last part of the test file; default: false")

    opt[Int]('c', "maxCloseDepth").action { (d, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(maxCloseDepth = d))
    }.text("maximum unfolding depth in the post-condition; default: 1")

    opt[Int]('o', "maxOpenDepth").action { (d, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(maxOpenDepth = d))
    }.text("maximum unfolding depth in the pre-condition; default: 1")

    opt[Boolean]('b', "branchAbduction").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(branchAbductionEnabled = b))
    }.text("abduce branches; default: false")

    help("help").text("prints this usage text")

    note("\nOnce the synthesis is done execution, statistics will be available in stats.csv (rewritten every time).\n")

  }
}
