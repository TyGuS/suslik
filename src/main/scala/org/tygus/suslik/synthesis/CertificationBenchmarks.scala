package org.tygus.suslik.synthesis

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Paths

import org.tygus.suslik.certification.source.SuslikProofStep
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

import scala.collection.mutable
import scala.io.StdIn
import scala.sys.process.Process

class CertificationBenchmarks(
                               targets: List[CertificationTarget],
                               params: SynConfig,
                               outputDirName: String,
                               statsFilePrefix: String
                              ) extends SynthesisRunnerUtil {
  val outputDir: File = new File(outputDirName)
  val synStatsFile = new File(List(outputDirName, s"$statsFilePrefix-syn.csv").mkString(File.separator))
  val certStatsFiles: Map[CertificationTarget, File] =
    targets.map(t => t -> new File(List(outputDirName, s"$statsFilePrefix-${t.name}.csv").mkString(File.separator))).toMap
  val defFilename: String = "common"
  val exclusions: List[(String, String)] = List(
    ("VST", "sll-bounds/sll-len"),
    ("VST", "tree/tree-size"),
    ("Iris", "sll-bounds/sll-max"),
    ("Iris", "sll-bounds/sll-min")
  )

  outputDir.mkdirs()
  initSynLog()
  targets.foreach(initCertLog)

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
          case trace: ProofTraceCert =>
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
    val outputDirs = targets.map { target =>
      val targetDir = Paths.get(outputDir.getPath, target.name, dir).toFile
      targetDir.mkdirs()
      target -> targetDir
    }.toMap

    if (testDir.exists() && testDir.isDirectory) {
      print(s"Retrieving definitions and specs from ${testDir.getName}...")
      val defs = getDefs(testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$defExtension")).toList)
      val tests = testDir.listFiles.filter(f => f.isFile
        && (f.getName.endsWith(s".$testExtension") ||
        f.getName.endsWith(s".$sketchExtension")))
        .map(f => getDescInputOutput(f.getAbsolutePath, params)).toList
      println("done!")

      val parser = new SSLParser

      println("Synthesizing specifications...")
      val synResults = for ((testName, _, in, _, params) <- tests) yield {
        val fullInput = List(defs, in).mkString("\n")
        print(s"  $testName...")
        val (res, env, synDuration) = synthesizeOne(fullInput, parser, params.copy(assertSuccess = false))
        println(s"done! (${fmtTime(synDuration)} s)")

        val root = CertTree.root.getOrElse(throw new Exception("Search tree is uninitialized"))
        val tree = SuslikProofStep.of_certtree(root)

        logSynStat(List(testName, fmtTime(synDuration)))

        (testName, res.head, tree, root.goal, env)
      }
      println("Finished synthesizing specifications!")

      for (target <- targets) {
        val outputDir = outputDirs(target)
        println(s"Generating ${target.name} certificates...")
        val certs = for ((testName, proc, tree, goal, env) <- synResults) yield {
          if (exclusions.contains((target.name, testName))) {
            print(s"  $testName...skipping unsupported test case for ${target.name}")
            None
          } else {
            try {
              print(s"  $testName...")
              val cert = target.certify(testName, proc, tree, goal, env)
              println("done!")
              Some(cert)
            } catch {
              case e: Throwable =>
                println(s"- ERR\n   failed to generate certificate for $testName (${e.getLocalizedMessage})")
                None
            }
          }
        }
        println(s"Finished generating ${target.name} certificates!")

        val validCerts = certs.filter(_.isDefined).map(_.get)
        val predicates = validCerts.flatMap(_.predicates).groupBy(_.name).map(_._2.head).toList
        println(s"Compiling ${target.name} common definitions to ${outputDir.getPath}...")
        val defFiles = target.generate_common_definitions_of(defFilename, predicates)
        defFiles.foreach { output =>
          print(s"  File ${output.filename}...")
          serialize(outputDir, output.filename, output.body)
          print("compiling...")
          output.compile(outputDir)
          println("done!")
        }
        println(s"Compiled ${target.name} common definitions to ${outputDir.getPath}!")

        println(s"Writing ${target.name} certificate outputs to ${outputDir.getPath}...")
        for (cert <- validCerts) {
          val outputs = cert.outputs_with_common_predicates(defFilename, predicates)
          for (o <- outputs) {
            print(s"  File ${o.filename}...")
            serialize(outputDir, o.filename, o.body)
            if (!o.isProof) {
              print("compiling...")
              o.compile(outputDir) match {
                case 0 => println("done!")
                case _ => println("ERR\n   Failed to compile common definition file!")
              }
            } else println("done!")
          }
          outputs.find(_.isProof) match {
            case None =>
              println(s"  Warning: No ${target.name} proof output found in certificate for ${cert.testName}! Skipping compilation.")
              logCertStat(target, List(cert.testName, "-", "-", "-", "-"))
            case Some(proof) =>
              print(s"  Checking size of main proof ${proof.filename}...")
              val (specSize, proofSize) = checkProofSize(outputDir, proof.filename)
              println(s"done! (spec: $specSize, proof: $proofSize)")
              print(s"  Compiling main proof ${proof.filename}...")
              val (res, compileTime) = timed(proof.compile(outputDir))
              val compileTimeOpt = if (res == 0) {
                println(s"done! (${fmtTime(compileTime)} s)")
                Some(compileTime)
              } else {
                println(s"ERR\n   Failed to compile ${proof.filename}!")
                None
              }
              logCertStat(target, List(
                cert.testName,
                proof.filename,
                specSize.toString,
                proofSize.toString,
                compileTimeOpt.map(fmtTime).getOrElse("-")
              ))
          }
        }
        println(s"Wrote ${target.name} certificate outputs to ${outputDir.getPath}!")
      }

      println("\n\n")
    } else {
      println(s"- ERR\n   no such test directory $testDir!")
    }
  }

  def serialize(dir: File, filename: String, body: String): Unit = {
    val file = Paths.get(dir.getCanonicalPath, filename).toFile
    new PrintWriter(file) {
      write(body); close()
    }
  }

  private def checkProofSize(dir: File, filename: String): (Int, Int) = {
    val cmd = Seq("coqwc", filename)
    val proofSizes = Process(cmd, dir).!!
    val Array(specSize, proofSize, _, _) = proofSizes.split('\n')(1).trim.split("\\s+")
    (specSize.toInt, proofSize.toInt)
  }

  private def initLog(file: File, header: List[String]): Unit = {
    if (file.exists()) file.delete()
    file.getParentFile.mkdirs()
    file.createNewFile()
    val data = header.mkString(", ") + "\n"
    SynStatUtil.using(new FileWriter(file, true))(_.write(data))
  }

  private def initSynLog(): Unit = {
    val header = List("Benchmark Name", "Synthesis Time (sec)")
    initLog(synStatsFile, header)
  }

  private def initCertLog(target: CertificationTarget): Unit = {
    val header = List("Benchmark Name", "File Name", "Spec Size", "Proof Size", "Proof Checking Time (sec)")
    initLog(certStatsFiles(target), header)
  }

  private def logStat(file: File, row: List[String]): Unit = {
    val data = s"${row.mkString(", ")}\n"
    SynStatUtil.using(new FileWriter(file, true))(_.write(data))
  }
  private def logSynStat(row: List[String]): Unit = logStat(synStatsFile, row)
  private def logCertStat(target: CertificationTarget, row: List[String]): Unit = logStat(certStatsFiles(target), row)

  private def fmtTime(ms: Long): String = "%.1f".format(ms.toDouble / 1000)
}

object CertificationBenchmarks {
  val allTargets = List(HTT(), VST(), Iris())
  val allStandard = List(
    "certification-benchmarks/ints",
    "certification-benchmarks/sll-bounds",
    "certification-benchmarks/sll",
    "certification-benchmarks/dll",
    "certification-benchmarks/tree"
  )
  val allAdvanced = List(
    "certification-benchmarks-advanced/bst",
    "certification-benchmarks-advanced/dll",
    "certification-benchmarks-advanced/srtl",
  )
  val defaultStandardConfig = BenchmarkConfig(allTargets, allStandard)
  val defaultAdvancedConfig = BenchmarkConfig(List(HTT()), allAdvanced)

  case class BenchmarkConfig(targets: List[CertificationTarget], groups: List[String]) {
    def updateTargets: BenchmarkConfig = {
      println(s"\nBenchmarks will be evaluated on target(s): ${targets.map(_.name).mkString(", ")}")
      val s = StdIn.readLine("Manually select targets instead? y/N: ")
      if (s.toLowerCase() == "y") {
        val newTargets = mutable.ListBuffer[CertificationTarget]()
        for (t <- targets) {
          val s = StdIn.readLine(s"Include target '${t.name}'? Y/n: ")
          if (s.toLowerCase() != "n") newTargets.append(t)
        }
        println(s"Benchmarks will be evaluated on target(s): ${newTargets.map(_.name).mkString(", ")}")
        this.copy(targets = newTargets.toList)
      } else {
        println("Evaluation targets unchanged.")
        this
      }
    }

    def updateGroups: BenchmarkConfig = {
      println("\nBenchmarks will be run on the following group(s):")
      for (g <- groups) println(s"- $g")
      val s = StdIn.readLine("Manually select groups instead? y/N: ")
      if (s.toLowerCase() == "y") {
        val newGroups = mutable.ListBuffer[String]()
        for (g <- groups) {
          val s = StdIn.readLine(s"Include group '$g'? Y/n: ")
          if (s.toLowerCase() != "n") newGroups.append(g)
        }
        println("Benchmarks will be run on the following group(s):")
        for (g <- newGroups) println(s"- $g")
        this.copy(groups = newGroups.toList)
      } else {
        println("Evaluation groups unchanged.")
        this
      }
    }
  }

  def main(args: Array[String]): Unit = {
    println("==========STANDARD BENCHMARK CONFIGURATION==========")
    val standardConfig = defaultStandardConfig.updateTargets.updateGroups
    println("\n\n==========ADVANCED BENCHMARK CONFIGURATION==========")
    val advancedConfig = defaultAdvancedConfig.updateGroups
    println("\n\nResults will be produced in the following directory:")
    println(s"  ${new File("certify").getCanonicalPath}")
    val s = StdIn.readLine("Existing files will be overwritten. Continue? Y/n: ")
    if (s.toLowerCase == "n") {
      println("Canceled job.")
      sys.exit(0)
    } else {
      println("Starting benchmarks...\n\n")
    }

    val standard = new CertificationBenchmarks (
      standardConfig.targets,
      SynConfig(certHammerPure = true),
      List("certify").mkString(File.separator),
      "standard"
    )
    standardConfig.groups.map(standard.runAllTestsFromDir)

    val advanced = new CertificationBenchmarks(
      advancedConfig.targets,
      SynConfig(certSetRepr = true),
      List("certify").mkString(File.separator),
      "advanced"
    )
    advancedConfig.groups.map(advanced.runAllTestsFromDir)
  }
}
