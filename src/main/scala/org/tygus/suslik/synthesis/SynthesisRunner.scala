package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.util.{SynLogLevels, SynLogging}

/**
  * @author Ilya Sergey
  */

object SynthesisRunner extends SynthesisRunnerUtil {

  // Enable verbose logging
  override implicit val log: SynLogging = SynLogLevels.Verbose

  import log._

  val synthesis: Synthesis = new PhasedSynthesis

  /**
    * Command line args:
    *
    * filePath                      a synthesis file name (the file under the specified folder, called filename.syn)
    *
    * -r, --trace <value>           print the entire derivation trace; default: false
    * -t, --timeout <value>         timeout for the derivation; default (in milliseconds): 300000 (5 min)
    * -d, --depth <value>           derivation depth; default: 100
    * -a, --assert <value>          check that the synthesized result against the expected one; default: false
    * -c, --maxCloseDepth <value>   maximum unfolding depth in the post-condition; default: 1
    * -o, --maxOpenDepth <value>    maximum unfolding depth in the pre-condition; default: 1
    * -b, --branchAbduction <value> abduct conditional branches; default: false
    * -f, --printFailed <value>     print failed rule applications; default: false
    *
    * --help                        prints the help reference
    *
    */
  def main(args: Array[String]): Unit = handleInput(args)

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig): Unit = {
    if (params.printStats) {
      println(desc)
      println()
    }
    try {
      synthesizeFromSpec(testName, in, out, params)
    } catch {
      case SynthesisException(msg) =>
        System.err.println("Synthesis failed:")
        System.err.println(msg)
    }
  }

  case class RunConfig(synConfig: SynConfig, fileName: String)

  val TOOLNAME = "SuSLik"
  val SCRIPTNAME = "suslik"
  private val VERSION = "0.1"
  private val VERSION_STRING = s"v$VERSION"

  private val defaultFile = List(".", "examples", "swap").mkString(File.separator)

  private def getParentDir(filePath: String): String = {
    val file = new File(filePath)
    if (!file.exists()) {
      "."
    }
    else file.getParentFile.getAbsolutePath
  }

  private def handleInput(args: Array[String]): Unit = {
    val newConfig = RunConfig(SynConfig(), defaultFile)
    parser.parse(args, newConfig) match {
      case Some(RunConfig(synConfig, file)) =>
        val dir = getParentDir(file)
        val fName = new File(file).getName
        runSingleTestFromDir(dir, fName, synConfig)
      case None =>
        System.err.println("Bad argument format.")
    }
  }

  private val parser = new {

  } with scopt.OptionParser[RunConfig](SCRIPTNAME) {
    // See examples at https://github.com/scopt/scopt

    head(TOOLNAME, VERSION_STRING)

    arg[String]("fileName").action {(x, c) =>
      c.copy(fileName = x)
    }.text("a synthesis file name (the file under the specified folder, called filename.syn)")

    opt[Boolean]('r', "trace").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printDerivations = b))
    }.text("print the entire derivation trace; default: true")

    opt[Long]('t', "timeout").action { (t, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(timeOut = t))
    }.text("timeout for the derivation; default (in milliseconds): 300000 (5 min)")

    opt[Boolean]('a', "assert").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(assertSuccess = b))
    }.text("check that the synthesized result against the expected one; default: true")

    opt[Int]('c', "maxCloseDepth").action { (d, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(maxCloseDepth = d))
    }.text("maximum unfolding depth in the post-condition; default: 1")

    opt[Int]('o', "maxOpenDepth").action { (d, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(maxOpenDepth = d))
    }.text("maximum unfolding depth in the pre-condition; default: 1")

    opt[Boolean]('x', "auxAbduction").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(auxAbduction = b))
    }.text("abduce auxiliary functions; default: false")

    opt[Boolean]('b', "branchAbduction").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(branchAbduction = b))
    }.text("abduce conditional branches; default: false")

    opt[Boolean](name = "commute").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(commute = b))
    }.text("only try commutative rule applications in one order; default: true")

    opt[Boolean](name = "phased").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(phased = b))
    }.text("split rules into unfolding and flat phases; default: true")

    opt[Boolean](name = "fail").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(fail = b))
    }.text("enable early failure rules; default: true")

    opt[Boolean](name = "invert").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(invert = b))
    }.text("enable invertible rules; default: true")

    opt[Boolean]('d', name = "depth").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(depthFirst = b))
    }.text("depth first search; default: true")

    opt[Boolean]('s', "printStats").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printStats = b))
    }.text("print synthesis stats; default: true")

    opt[Boolean]('e', "printEnv").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printEnv = b))
    }.text("print synthesis context; default: false")

    opt[Boolean]('f', "printFail").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printFailed = b))
    }.text("print failed rule applications; default: false")

    opt[Boolean]('g', "tags").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printTags = b))
    }.text("print predicate application tags in derivations; default: false")

    opt[Boolean]('l', "log").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(logToFile = b))
    }.text("log results to a csv file; default: true")

    opt[Boolean](name="memoization").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(memoization = b))
    }.text("enable memoization; default: true")


    help("help").text("prints this usage text")

    note("\nOnce the synthesis is done execution, statistics will be available in stats.csv (rewritten every time).\n")

  }

  def parseParams(paramString: Array[String], params: SynConfig): SynConfig = {
    val newConfig = RunConfig(params, defaultFile)
    parser.parse(paramString, newConfig) match {
      case Some(RunConfig(synConfig, _)) => synConfig
      case None => throw SynthesisException("Bad argument format.")
    }
  }
}
