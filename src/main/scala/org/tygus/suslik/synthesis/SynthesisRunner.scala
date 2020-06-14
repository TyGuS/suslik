package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.certification.targets._
import org.tygus.suslik.util.{SynLogLevels, SynLogging}

/**
  * @author Ilya Sergey
  */

object SynthesisRunner extends SynthesisRunnerUtil {

  // Enable verbose logging
  override implicit val log: SynLogging = SynLogLevels.Verbose

  import log._

  /**
    * Command line args:
    *
    * fileName                       a synthesis file name (the file under the specified folder, called filename.syn)
    *
    * -r, --trace <value>            print the entire derivation trace; default: true
    * -t, --timeout <value>          timeout for the derivation; default (in milliseconds): 300000 (5 min)
    * -a, --assert <value>           check that the synthesized result against the expected one; default: true
    * -c, --maxCloseDepth <value>    maximum unfolding depth in the post-condition; default: 1
    * -o, --maxOpenDepth <value>     maximum unfolding depth in the pre-condition; default: 1
    * -x, --auxAbduction <value>     abduce auxiliary functions; default: false
    * -b, --branchAbduction <value>  abduce conditional branches; default: false
    * --phased <value>               split rules into unfolding and flat phases; default: true
    * -d, --depth <value>            depth first search; default: false
    * -i, --interactive <value>      interactive mode; default: false
    * -s, --printStats <value>       print synthesis stats; default: true
    * -e, --printEnv <value>         print synthesis context; default: false
    * -f, --printFail <value>        print failed rule applications; default: false
    * -l, --log <value>              log results to a csv file; default: true
    * --memoization <value>          enable memoization; default: true
    * --certTarget <value>           set certification target; default: none
    * --certDest <value>             write certificate to path; default: none
    *
    * --help                         prints the help reference
    *
    */
  def main(args: Array[String]): Unit = handleInput(args)

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
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

    implicit val certTargetRead: scopt.Read[CertificationTarget] =
      scopt.Read.reads {
        case "coq" => coq.Coq
        case _ => ???
      }

    arg[String]("fileName").action { (x, c) =>
      c.copy(fileName = x)
    }.text("a synthesis file name (the file under the specified folder, called filename.syn)")

    opt[Boolean]('r', "trace").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printDerivations = b))
    }.text("print the entire derivation trace; default: false")

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

    opt[Boolean](name = "phased").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(phased = b))
    }.text("split rules into unfolding and flat phases; default: true")

    opt[Boolean]('d', name = "depth").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(depthFirst = b))
    }.text("depth first search; default: false")

    opt[Boolean]('i', "interactive").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(interactive = b))
    }.text("interactive mode; default: false")

    opt[Boolean]('s', "printStats").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printStats = b))
    }.text("print synthesis stats; default: false")

    opt[Boolean]('p', "printSpecs").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printSpecs = b))
    }.text("print specifications for synthesized functions; default: false")

    opt[Boolean]('e', "printEnv").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printEnv = b))
    }.text("print synthesis context; default: false")

    opt[Boolean]('f', "printFail").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printFailed = b))
    }.text("print failed rule applications; default: false")

    opt[Boolean]('l', "log").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(logToFile = b))
    }.text("log results to a csv file; default: false")

    opt[Boolean](name = "memoization").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(memoization = b))
    }.text("enable memoization; default: true")

    opt[CertificationTarget](name="certTarget").action { (t, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(certTarget = t))
    }.text("set certification target; default: none")

    opt[File](name="certDest").action { (f, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(certDest = f))
    }.text("write certificate to path; default: none")

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
