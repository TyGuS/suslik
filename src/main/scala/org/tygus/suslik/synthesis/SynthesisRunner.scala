package org.tygus.suslik.synthesis

import java.io.File
import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.certification.CertificationTarget.NoCert
import org.tygus.suslik.certification.targets._
import org.tygus.suslik.interaction.SynthesisServer
import org.tygus.suslik.report.Log
import org.tygus.suslik.util.SynLogLevels
import scopt.OptionParser

import scala.concurrent.duration.{Duration, MILLISECONDS}

/**
  * @author Ilya Sergey
  */

object SynthesisRunner extends SynthesisRunnerUtil {

  // Enable verbose logging
  override implicit val log: Log = new Log(SynLogLevels.Verbose)

  /**
    * Command line args:
    *
    * fileName                       a synthesis file name (the file under the specified folder, called filename.syn)
    *
    * -r, --trace <value>            print the entire derivation trace; default: false
    * -t, --timeout <value>          timeout for the derivation; default (in milliseconds): 300000 (5 min)
    * -a, --assert <value>           check that the synthesized result against the expected one; default: false
    * -c, --maxCloseDepth <value>    maximum unfolding depth in the post-condition; default: 1
    * -o, --maxOpenDepth <value>     maximum unfolding depth in the pre-condition; default: 1
    * -f, --maxCallDepth <value>     maximum call depth; default: 1
    * -x, --auxAbduction <value>     abduce auxiliary functions; default: false
    * --topLevelRecursion <value>    allow top-level recursion; default: true
    * -b, --branchAbduction <value>  abduce conditional branches; default: false
    * --maxGuardConjuncts <value>    maximum number of conjuncts in an abduced guard; default: 2
    * --phased <value>               split rules into unfolding and flat phases; default: true
    * -d, --dfs <value>              depth first search; default: false
    * --bfs <value>                  breadth first search (ignore weights); default: false
    * --delegate <value>             delegate pure synthesis to CVC4; default: true
    * -i, --interactive <value>      interactive mode; default: false
    * -s, --printStats <value>       print synthesis stats; default: false
    * -p, --printSpecs <value>       print specifications for synthesized functions; default: false
    * -e, --printEnv <value>         print synthesis context; default: false
    * --printFail <value>            print failed rule applications; default: false
    * -l, --log <value>              log results to a csv file; default: false
    * -j, --traceToJsonFile <value>  dump entire proof search trace to a json file; default: none
    * --memo <value>                 enable memoization; default: true
    * --lexi <value>                 use lexicographic termination metric (as opposed to total size); default: false
    * --certTarget <value>           set certification target; default: none (options: htt | vst | iris)
    * --certDest <value>             specify the directory in which to store the certificate file; default: none
    * --certHammerPure <value>       use hammer to solve pure lemmas instead of admitting them (HTT only); default: false
    * --certSetRepr <value>          use SSReflect's perm_eq to represent set equality (HTT only); default: false
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
        System.err.println(msg)
      case SynTimeOutException(msg) =>
        System.err.println(msg)
    }
  }

  case class RunConfig(synConfig: SynConfig, fileName: String, mode: String = "batch")

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
      case Some(RunConfig(synConfig, file, "batch")) =>
        val dir = getParentDir(file)
        val fName = new File(file).getName
        runSingleTestFromDir(dir, fName, synConfig)
      case Some(RunConfig(synConfig, _, "server")) =>
        new SynthesisServer().start() /** @todo use config! */
      case _ =>
        System.err.println("Bad argument format.")
    }
  }

  private val parser: OptionParser[RunConfig] = new scopt.OptionParser[RunConfig](SCRIPTNAME) {
    // See examples at https://github.com/scopt/scopt

    head(TOOLNAME, VERSION_STRING)

    implicit val certTargetRead: scopt.Read[CertificationTarget] =
      scopt.Read.reads {
        case "htt" => htt.HTT()
        case "vst" => vst.VST()
        case "iris" => iris.Iris()
        case _ => NoCert
      }

    implicit val durationRead: scopt.Read[Duration] =
      scopt.Read.reads { s =>
        try { Duration(s.toLong, MILLISECONDS) /** @todo make default be seconds? */ }
        catch { case _: NumberFormatException => Duration(s) }
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

    opt[Duration]('t', "timeout").action(cfg { t =>
      _.copy(timeOut = t.toMillis)
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

    opt[Unit](name = "simple").action(cfg { _ =>
      _.copy(simple = true)
    }).text("use simple, unphased rules (this is very slow); default: no")

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
    }.text("set certification target; default: none (options: htt | vst | iris)")

    opt[File](name="certDest").action(cfg { f =>
      _.copy(certDest = f)
    }).text("specify the directory in which to store the certificate file; default: none")

    opt[Boolean](name = "certHammerPure").action(cfg { b =>
      _.copy(certHammerPure = b)
    }).text("use hammer to solve pure lemmas instead of admitting them (HTT only); default: false")

    opt[Boolean](name = "certSetRepr").action(cfg { b =>
      _.copy(certSetRepr = b)
    }).text("use SSReflect's perm_eq to represent set equality (HTT only); default: false")

    help("help").text("prints this usage text")

    note("\nOnce the synthesis is done execution, statistics will be available in stats.csv (rewritten every time).\n")

    cmd("server")
      .text("run a Web server for interactive mode")
      .action((_, c) => c.copy(mode = "server"))
  }

  def parseParams(paramString: Array[String], params: SynConfig): SynConfig = {
    val newConfig = RunConfig(params, defaultFile)
    parser.parse(paramString, newConfig) match {
      case Some(RunConfig(synConfig, _, _)) => synConfig
      case None => throw SynthesisException("Bad argument format.")
    }
  }
}
