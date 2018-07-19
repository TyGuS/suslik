package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.logic.Resolver._
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.util.{SynLogLevels, SynLogging, SynStatUtil}

import scala.io.Source

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait SynthesisRunnerUtil {

  implicit val log : SynLogging = SynLogLevels.Test
  import log._

  val testSeparator = "###"
  val testExtension = "syn"
  val defExtension = "def"
  val paramPrefix = "#"

  // The path starts from the project root.
  val rootDir: String = "./src/test/resources/synthesis".replace("/", File.separator)

  val synthesis: Synthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit

  import synthesis._
  
  def getDescInputOutput(testFilePath: String, initialParams: SynConfig = defaultConfig): (String, String, String, String, SynConfig) = {
    val file = new File(testFilePath)
    // The path is counted from the rout
    val allLines = Source.fromFile(file).getLines.toList
    val (params, lines) =
      if (allLines.nonEmpty && allLines.head.startsWith(paramPrefix)) {
        (SynthesisRunner.parseParams(allLines.head.drop(paramPrefix.length).split(' '), initialParams), allLines.tail)
      } else (defaultConfig, allLines)
    val i = lines.indexWhere(_.trim.contains(testSeparator))
    val (l1, l2) = lines.splitAt(i)
    val fname = removeSuffix(file.getName, s".$testExtension")
    val dirName = file.getParentFile.getName
    val description = if (l1.isEmpty) "Testing synthesis" else l1.mkString("\n").trim
    // The first part is the description
    val testName = s"$dirName/$fname"
    val desc = s"[$testName] $description"

    val remainder = l2.tail
    // The remainder is the input and output
    val j = remainder.indexWhere(_.trim.startsWith(testSeparator))
    val (l3, l4) = remainder.splitAt(j)
    val input = l3.mkString(" ").trim
    val output = l4.tail.mkString("\n").trim
    (testName, desc, input, output, params)
  }

  def synthesizeFromFile(dir: String, testName: String): Unit = {
    val (_, desc, in, out, params) = getDescInputOutput(testName)
    synthesizeFromSpec(testName, in, out, params)
  }

  def synthesizeFromSpec(testName: String, text: String, out: String = "nope", params: SynConfig = defaultConfig) : Unit = {
    val parser = new SSLParser
    val res = parser.parseGoal(text)
    if (!res.successful) {
      throw SynthesisException(s"Failed to parse the input.")
    }

    val prog = res.get
    // assert(prog.predicates.nonEmpty)
    val (specs, env) = resolveProgram(prog)

    if (specs.lengthCompare(1) != 0) {
      throw SynthesisException("Expected a single synthesis goal")
    }

    val spec = specs.head
    val time1 = System.currentTimeMillis()
    val sresult = synthesizeProc(spec, env.copy(config = params))
    val time2 = System.currentTimeMillis()
    val delta = time2 - time1

    SynStatUtil.log(testName, delta, params, spec, sresult)

    sresult match {
      case Some((rr, stats)) =>
        val result = rr.pp
        if (params.printStats) {
          testPrintln(s"\n[$testName]:", Console.MAGENTA)
          testPrintln(params.pp)
          testPrintln(s"${spec.pp}\n", Console.BLUE)
          testPrintln(s"Successfully synthesised in $delta milliseconds:", Console.GREEN)
          testPrintln(s"Number of backtrackings ${stats.numBack}")
          testPrintln(s"Lasting successful rule applications: ${stats.numLasting}")
          testPrintln(s"Total successful rule applications: ${stats.numSucc}")
          testPrintln(s"Final size of SMT cache: ${stats.smtCacheSize}")
          testPrintln(result)
          testPrintln("-----------------------------------------------------")
        } else {
          println(result)
        }
        if (out != "nope") {
          val tt = out.trim.lines.toList
          val res = result.trim.lines.toList
          if (params.assertSuccess && res != tt) {
            throw SynthesisException(s"\nThe expected output\n$tt\ndoesn't match the result:\n$res")
          }
        }
      case None =>
        throw SynthesisException(s"Failed to synthesise:\n$sresult")
    }
  }


  def getDefs(defFiles: List[File]): String = {
    if (defFiles.isEmpty) return ""
    assert(defFiles.size == 1, "More than one file with definitions in the folder")
    val file = new File(defFiles.head.getAbsolutePath)
    Source.fromFile(file).getLines.toList.mkString("\n")
  }

  def runAllTestsFromDir(dir: String) {
    val path = List(rootDir, dir).mkString(File.separator)
    val testDir = new File(path)
    if (testDir.exists() && testDir.isDirectory) {
      // Create log file
      SynStatUtil.init(defaultConfig)
      // Get definitions
      val defs = getDefs(testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$defExtension")).toList)
      // Get specs
      val tests = testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$testExtension")).toList
      for (f <- tests) {
        val (testName, desc, in, out, params) = getDescInputOutput(f.getAbsolutePath)
        val fullInput = List(defs, in).mkString("\n")
        doRun(testName, desc, fullInput, out, params)
      }
    }
  }

  def runSingleTestFromDir(dir: String, fname: String, params: SynConfig = defaultConfig) {
    var testDir = new File(dir)
    if (!testDir.exists()) {
      val path = List(rootDir, dir).mkString(File.separator)
      println(s"Trying the path $path")
      testDir = new File(path)
      if (!testDir.exists()) {
        System.err.println(s"Found no directory $dir.")
        return
      }
    }
    if (testDir.exists() && testDir.isDirectory) {
      // Maybe create log file (depending on params)
      SynStatUtil.init(params)
      // Get definitions
      val defs = getDefs(testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$defExtension")).toList)
      // Get specs
      val tests = testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$testExtension")).toList
      tests.find(f => removeSuffix(f.getName, s".$testExtension") == fname) match {
        case Some(f) =>
          val (testName, desc, in, out, allParams) = getDescInputOutput(f.getAbsolutePath, params)
          val fullInput = List(defs, in).mkString("\n")
          doRun(testName, desc, fullInput, out, allParams)
        case None =>
          System.err.println(s"No file with the name $fname.syn found in the directory $dir.")
      }
    }
  }


  def removeSuffix(s: String, suffix: String): String = {
    if (s.endsWith(suffix)) s.substring(0, s.length - suffix.length) else s
  }

}

