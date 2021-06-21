package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.certification.targets._
import org.tygus.suslik.report.Log
import org.tygus.suslik.util.SynLogLevels
import scopt.OptionParser

/**
  * @author Ilya Sergey
  */

object SynthesisRunner extends SynthesisRunnerUtil {

  // Enable verbose logging
  override implicit val log = new Log(SynLogLevels.Verbose)

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
    * -j, --traceToJson <filename>   dump entire proof search trace to a json file; default: none
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
  private val VERSION = "0.5"
  private val VERSION_STRING = s"v$VERSION"

  private val defaultFile = List(".", "examples", "swap").mkString(File.separator)

  private def getParentDir(filePath: String): String = {
    val file = new File(filePath)
    if (file.exists()) file.getParentFile.getAbsolutePath
    else file.getParent
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

  private val parser: OptionParser[RunConfig] = new scopt.OptionParser[RunConfig](SCRIPTNAME) {
    // See examples at https://github.com/scopt/scopt

    head(TOOLNAME, VERSION_STRING)

    implicit val certTargetRead: scopt.Read[CertificationTarget] =
      scopt.Read.reads {
        case "coq" => coq.Coq
        case t => throw SynthesisException(s"Certification target $t is not supported") 
      }

    private def uncurryLens[A,B,C](lens: scalaz.Lens[A, B])(f: C => B => B) =
      Function.uncurried { c:C => lens =>= f(c) }

    private val configLens = scalaz.Lens.lensu[RunConfig, SynConfig](
      (c, v) => c.copy(synConfig = v), _.synConfig)
    private def cfg[C](f:C => SynConfig => SynConfig) = uncurryLens(configLens)(f)

    arg[String]("fileName").action { (x, c) =>
      c.copy(fileName = x)
    }.text("a synthesis file name (the file under the specified folder, called filename.syn)")

    opt[Int]('r', "trace").action(cfg { l =>
      _.copy(traceLevel = l)
    }).text("print the entire derivation trace; default: false")

    opt[Long]('t', "timeout").action(cfg { t =>
      _.copy(timeOut = t)
    }).text("timeout for the derivation; default (in milliseconds): 1800000 (30 min)")

    opt[Boolean]('a', "assert").action(cfg { b =>
      _.copy(assertSuccess = b)
    }).text("check that the synthesized result against the expected one; default: false")

    opt[Int]('c', "maxCloseDepth").action(cfg { d =>
      _.copy(maxCloseDepth = d)
    }).text("maximum unfolding depth in the post-condition; default: 1")

    opt[Int]('o', "maxOpenDepth").action(cfg { d =>
      _.copy(maxOpenDepth = d)
    }).text("maximum unfolding depth in the pre-condition; default: 1")

    opt[Int]('f', "maxCallDepth").action(cfg { d =>
      _.copy(maxCalls = d)
    }).text("maximum call depth; default: 2")

    opt[Boolean]('x', "auxAbduction").action(cfg { b =>
      _.copy(auxAbduction = b)
    }).text("abduce auxiliary functions; default: true")

    opt[Boolean]('b', "branchAbduction").action(cfg { b =>
      _.copy(branchAbduction = b)
    }).text("abduce conditional branches; default: false")

    opt[Int]("maxGuardConjuncts").action(cfg { n =>
      _.copy(maxGuardConjuncts = n)
    }).text("maximum number of conjuncts in an abduced guard; default: 2")

    opt[Boolean]('d', name = "dfs").action(cfg { b =>
      _.copy(depthFirst = b)
    }).text("depth first search; default: false")

    opt[Boolean](name = "bfs").action(cfg { b =>
      _.copy(breadthFirst = b)
    }).text("breadth first search (ignore weights); default: false")

    opt[Boolean](name = "delegate").action(cfg { b =>
      _.copy(delegatePure = b)
    }).text("delegate pure synthesis to CVC4; default: false")

    opt[Boolean](name = "extended").action(cfg { b =>
      conf => conf.copy(extendedPure = b, delegatePure = b || conf.delegatePure)
    }).text("use extended search space for pure synthesis with CVC4; default: false")

    opt[Boolean](name = "simple").action(cfg { b =>
      _.copy(simple = b)
    }).text("use simple, unphased rules (this is very slow); default: false")

    opt[Boolean]('i', "interactive").action(cfg { b =>
      _.copy(interactive = b)
    }).text("interactive mode; default: false")

    opt[Boolean]('s', "printStats").action(cfg { b =>
      _.copy(printStats = b)
    }).text("print synthesis stats; default: false")

    opt[Boolean]('p', "printSpecs").action { (b, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(printSpecs = b))
    }.text("print specifications for synthesized functions; default: true")

    opt[Boolean]('l', "log").action(cfg { b =>
      _.copy(logToFile = b)
    }).text("log results to a csv file; default: false")

    opt[String]('j', "traceToJson").action(cfg { fn =>
      _.copy(traceToJsonFile = Some(new File(fn)))
    }).text("dump entire proof search trace to a json file; default: none")

    opt[Boolean](name = "memo").action(cfg { b =>
      _.copy(memoization = b)
    }).text("enable memoization; default: true")

    opt[CertificationTarget](name="certTarget").action { (t, rc) =>
      rc.copy(synConfig = rc.synConfig.copy(certTarget = t))
    }.text("set certification target; default: none")

    opt[File](name="certDest").action(cfg { f =>
      _.copy(certDest = f)
    }).text("write certificate to path; default: none")

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
