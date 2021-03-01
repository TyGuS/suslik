package org.tygus.suslik.synthesis

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.{Files, Paths}

import org.tygus.suslik.certification.targets.htt.HTT
import org.tygus.suslik.certification.targets.vst.VST
import org.tygus.suslik.certification.targets.iris.Iris
import org.tygus.suslik.certification.{CertTree, CertificationTarget}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.logic.Preprocessor.preprocessProgram
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.report.ProofTraceCert
import org.tygus.suslik.report.StopWatch.timed
import org.tygus.suslik.synthesis.tactics.PhasedSynthesis
import org.tygus.suslik.util.{SynStatUtil, SynStats}

import scala.sys.process._

abstract class CertificationBenchmarks extends SynthesisRunnerUtil {
  val targets: List[CertificationTarget]
  val statsFile: File = new File("cert-stats.csv")
  val defFilename: String = "common"

  def synthesizeOne(text: String, parser: SSLParser, params: SynConfig): (List[Statements.Procedure], Environment, Long) = {
    val res = params.inputFormat match {
      case `dotSyn` => parser.parseGoalSYN(text)
      case `dotSus` => parser.parseGoalSUS(text)
    }
    if (!res.successful) {
      throw SynthesisException(s"Failed to parse the input:\n$res")
    }

    val prog = res.get
    val (specs, predEnv, funcEnv, body) = preprocessProgram(prog, params)

    if (specs.lengthCompare(1) != 0) {
      throw SynthesisException("Expected a single synthesis goal")
    }

    val spec = specs.head
    val env = Environment(predEnv, funcEnv, params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)

    env.stats.start()
    val sresult = synthesizer.synthesizeProc(spec, env, body)

    sresult._1 match {
      case Nil =>
        throw SynthesisException(s"Failed to synthesise:\n$sresult")
      case procs =>
        synthesizer.trace match {
          case trace:ProofTraceCert =>
            CertTree.fromTrace(trace)
          case _ =>
        }
        val duration = env.stats.duration
        (procs, env, duration)
    }
  }

  override def createSynthesizer(env: Environment): Synthesis = {
    val tactic = new PhasedSynthesis(env.config)
    val trace = new ProofTraceCert()
    new Synthesis(tactic, log, trace)
  }

  override def runAllTestsFromDir(dir: String): Unit = {
    println(s"=========================================\n")
    println(s"  Benchmark Group: $dir\n")
    println(s"=========================================\n")
    val path = List(rootDir, dir).mkString(File.separator)
    val testDir = new File(path)
    val tempDirNames = targets.map(t => t -> Files.createTempDirectory("suslik-").toFile).toMap

    if (testDir.exists() && testDir.isDirectory) {
      print(s"Retrieving definitions and specs from ${testDir.getName}...")
      val defs = getDefs(testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$defExtension")).toList)
      val tests = testDir.listFiles.filter(f => f.isFile
        && (f.getName.endsWith(s".$testExtension") ||
        f.getName.endsWith(s".$sketchExtension"))).toList
      println("done!")

      val parser = new SSLParser

      val testCases = for (f <- tests) yield {
        val (testName, desc, in, out, params) = getDescInputOutput(f.getAbsolutePath)
        (testName, in, params)
      }

      val results = targets.map(target => {
        val tempDir = tempDirNames(target)
        println(s"\n****************************************\n")
        println(s"Running benchmarks for certification target: ${target.name}")
        println(s"Initialized output directory: ${tempDir.getCanonicalPath}\n")

        println(s"Synthesizing ${tests.length} test cases...")

        val synResults = for ((testName, in, params) <- testCases)  yield {
          println(s"$testName:")
          val fullInput = List(defs, in).mkString("\n")

          print(s"  synthesizing in certification mode...")
          val (res, env, synDuration) = synthesizeOne(fullInput, parser, params.copy(assertSuccess = false))
          println(s"done! (${fmtTime(synDuration)} s)")

          print(s"  generating certificate...")
          try {
            val (cert, proofGenDuration) = timed(target.certify(res.head, env))
            println("done!")
            (testName, synDuration, Some(cert, proofGenDuration))
          } catch {
            case e =>
              println(s"- ERR\n   failed to generate certificate for ${testName} (${e.getLocalizedMessage})")
              (testName, synDuration, None)
          }
        }

        println(s"Successfully synthesized ${tests.length} tests.")

        val validCerts = synResults.map(_._3).filter(_.isDefined).map(_.get).map(_._1)
        val predicates = validCerts.flatMap(_.predicates).groupBy(_.name).map(_._2.head).toList
        val defFiles = target.generate_common_definitions_of(defFilename, predicates)
        defFiles.foreach {
          case output =>
            print(s"\nWriting common definitions to file $tempDir/${output.filename}...")
            serialize(tempDir, output.filename, output.body)
        }
        println("done!")
        print(s"Compiling definitions...")
        defFiles.foreach(output => output.compile(tempDir))
        println("done!")

        println(s"\nGenerating statistics...")
        val testToStats = synResults.map { case (testName, synDuration, certOpt) => certOpt match {
          case None =>
            println(s"$testName:")
            println("  No certificate was generated; skipping proof check...")
            testName -> (synDuration, None, None, None)
          case Some((cert, proofGenDuration)) =>
            println(s"$testName:")

            val outputs = cert.outputs_with_common_predicates(defFilename, predicates)
            for (o <- outputs) yield {
              print(s"  Writing certificate output to file ${o.filename}...")
              serialize(tempDir, o.filename, o.body)
              println("done!")
              if (!o.isProof) {
                print(s"  Compiling output...")
                o.compile(tempDir)
                println("done!")
              }
            }

           outputs.find(_.isProof) match {
              case Some(proof) =>
                print(s"  Checking proof size...")
                val (specSize, proofSize) = checkProofSize(tempDir, proof.filename)
                println(s"done! (spec: $specSize, proof: $proofSize)")
                print(s"  Compiling proof...")
                val (res, proofCheckDuration) = timed (proof.compile(tempDir))
                if (res == 0) {
                  println(s"done! (${fmtTime(proofCheckDuration)} s)")
                  testName -> (synDuration, Some(proofGenDuration), Some(specSize, proofSize), Some(proofCheckDuration))
                } else {
                  println(s"ERR\n   Failed to verify ${proof.filename}!")
                  testName -> (synDuration, Some(proofGenDuration), Some(specSize, proofSize), None)
                }
              case None =>
                println(s"Certificate was generated, but no proof output was found; skipping verification...")
                testName -> (synDuration, Some(proofGenDuration), None, None)
            }
        }}.toMap
        println(s"\n****************************************\n")

        target -> testToStats
      }).toMap

      for ((testName, _, _) <- testCases) {
        val resultsByTarget = targets.map(target => results(target)(testName))
        logStat(testName, resultsByTarget)
      }

      println(s"\nStatistics written to: ${statsFile.getCanonicalPath}\n\n")
    }
  }

  private def serialize(dir: File, filename: String, body: String): Unit = {
    val file = Paths.get(dir.getCanonicalPath, filename).toFile
    new PrintWriter(file) { write(body); close() }
  }

  private def checkProofSize(dir: File, filename: String): (Int, Int) = {
    val cmd = Seq("coqwc", filename)
    val proofSizes = Process(cmd, dir).!!
    val Array(specSize, proofSize, _, _) = proofSizes.split('\n')(1).trim.split("\\s+")
    (specSize.toInt, proofSize.toInt)
  }

  def initLog(): Unit = {
    if (statsFile.exists()) statsFile.delete()
    statsFile.createNewFile()
    val topLevelHeader = List("") ++ targets.flatMap(t => List(t.name, "", "", "", ""))
    val targetHeader = List("Synthesis Time (sec)", "Proof Generation Time (sec)", "Proof Checking Time (sec)", "Spec Size", "Proof Size")
    val targetHeaders = targets.flatMap(_ => targetHeader)
    val statsHeader = topLevelHeader.mkString(", ") + "\n" + (List("Benchmark Name") ++ targetHeaders).mkString(", ") + "\n"
    SynStatUtil.using(new FileWriter(statsFile, true))(_.write(statsHeader))
  }

  private def logStat(name: String, targetResults: List[(Long, Option[Long], Option[(Int, Int)], Option[Long])]): Unit = {
    def ppRes(res: (Long, Option[Long], Option[(Int, Int)], Option[Long])): String = {
      val (synDuration, proofGenDuration, proofStats, proofCheckDuration) = res
      val proofGenStr = proofGenDuration.map(fmtTime).getOrElse("-")
      val proofStatsStr = proofStats match {
        case Some((specSize, proofSize)) => List(specSize, proofSize).mkString(", ")
        case None => "-, -, -"
      }
      val proofCheckStr = proofCheckDuration.map(fmtTime).getOrElse("-")
      s"${fmtTime(synDuration)}, $proofGenStr, $proofCheckStr, $proofStatsStr"
    }
    val data = s"$name, ${targetResults.map(ppRes).mkString(", ")}\n"
    SynStatUtil.using(new FileWriter(statsFile, true))(_.write(data))
  }

  private def fmtTime(ms: Long): String = "%.1f".format(ms.toDouble / 1000)
}

object CertificationBenchmarks {
  def main(args: Array[String]): Unit = {
    val benchmarks = new CertificationBenchmarks {
      override val targets: List[CertificationTarget] = List(HTT(), VST(), Iris())
    }
    benchmarks.runAllTestsFromDir("certification/ints")
    benchmarks.runAllTestsFromDir("certification/sll-bounds")
    benchmarks.runAllTestsFromDir("certification/sll")
    benchmarks.runAllTestsFromDir("certification/dll")
    benchmarks.runAllTestsFromDir("certification/srtl")
    benchmarks.runAllTestsFromDir("certification/tree")
    benchmarks.runAllTestsFromDir("certification/bst")
  }
}