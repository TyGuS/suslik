package org.tygus.suslik.synthesis

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.{Files, Paths}

import org.tygus.suslik.certification.{CertTree, CertificationTarget, CoqOutput}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.logic.Preprocessor.preprocessProgram
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.report.ProofTraceCert
import org.tygus.suslik.report.StopWatch.timed
import org.tygus.suslik.util.{SynStatUtil, SynStats}

import scala.sys.process._

abstract class CertificationBenchmarks extends SynthesisRunnerUtil {
  val target: CertificationTarget
  val tempDir: File = Files.createTempDirectory("suslik-").toFile
  val defFilename: String = "common.v"
  val statsFile: File = new File("cert-stats.csv")
  val statsHeader: String = List("Benchmark Name", "Output Name", "Synthesis Time (sec)", "Proof Time (sec)", "Spec Size", "Proof Size").mkString(", ") + "\n"

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
    val duration = env.stats.duration

    sresult._1 match {
      case Nil =>
        throw SynthesisException(s"Failed to synthesise:\n$sresult")
      case procs =>
        synthesizer.trace match {
          case trace:ProofTraceCert =>
            CertTree.fromTrace(trace)
          case _ =>
        }
        (procs, env, duration)
    }
  }

  override def runAllTestsFromDir(dir: String): Unit = {
    println(s"==========Benchmark Group $dir==========\n")
    val path = List(rootDir, dir).mkString(File.separator)
    val testDir = new File(path)
    if (testDir.exists() && testDir.isDirectory) {
      print(s"Retrieving definitions and specs from ${testDir.getName}...")
      val defs = getDefs(testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$defExtension")).toList)
      val tests = testDir.listFiles.filter(f => f.isFile
        && (f.getName.endsWith(s".$testExtension") ||
        f.getName.endsWith(s".$sketchExtension"))).toList
      println("done!")

      val parser = new SSLParser
      println(s"\nSynthesizing ${tests.length} test cases...")
      val synResults = for (f <- tests) yield {
        val (testName, desc, in, out, params) = getDescInputOutput(f.getAbsolutePath)
        println(s"$testName:")
        val fullInput = List(defs, in).mkString("\n")

        print(s"  synthesizing in certification mode...")
        val (res, env, synDuration) = synthesizeOne(fullInput, parser, params.copy(assertSuccess = false, certTarget = target, certDest = tempDir))
        println(s"done! (${fmtTime(synDuration)} s)")

        print(s"  generating certificate...")
        val cert = target.certify(res.head, env)
        println("done!")
        (testName, cert, synDuration)
      }

      println(s"Successfully synthesized ${tests.length} tests.")

      print(s"\nWriting definitions to file $defFilename...")
      val predicates = synResults.flatMap(_._2.predicates).groupBy(_.name).map(_._2.head).toList
      val defFile = CoqOutput(defFilename, "common", target.mkDefs(predicates))
      serialize(tempDir, defFilename, defFile.body)
      println("done!")
      print(s"Compiling $defFilename...")
      defFile.compile(tempDir)
      println("done!")

      println(s"\nGenerating statistics...")
      for ((testName, cert, synDuration) <- synResults) {
        println(s"$testName:")
        for (o <- cert.outputs) yield {
          print(s"  Writing certificate output to file ${o.filename}...")
          serialize(tempDir, o.filename, o.body)
          println("done!")
          if (o.isProof) {
            print(s"  Checking proof size...")
            val (specSize, proofSize) = checkProofSize(tempDir, o.filename)
            println(s"done! (spec: $specSize, proof: $proofSize)")
            print(s"  Compiling proof...")
            val (res, proofDuration) = timed (o.compile(tempDir))
            if (res == 0) {
              println(s"done! (${fmtTime(proofDuration)} s)")
              logStat(testName, o.filename, synDuration, proofDuration, specSize, proofSize)
            } else {
              throw SynthesisException(s"Failed to verify ${o.filename}!")
            }
          } else {
            print(s"  Compiling output...")
            o.compile(tempDir)
            println("done!")
          }
        }
      }

      println(s"\nStatistics written to: ${statsFile.getCanonicalPath}")
      println(s"Proofs and definitions written to: $tempDir\n\n")
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
    SynStatUtil.using(new FileWriter(statsFile, true))(_.write(statsHeader))
  }

  private def logStat(name: String, filename: String, synDuration: Long, proofDuration: Long, specSize: Int, proofSize: Int): Unit = {
    val data = s"$name, $filename, ${fmtTime(synDuration)}, ${fmtTime(proofDuration)}, $specSize, $proofSize\n"
    SynStatUtil.using(new FileWriter(statsFile, true))(_.write(data))
  }

  private def fmtTime(ms: Long): String = "%.1f".format(ms.toDouble / 1000)
}
