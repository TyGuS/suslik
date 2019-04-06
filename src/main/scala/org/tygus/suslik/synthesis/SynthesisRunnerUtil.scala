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
  val sketchExtension = "sus"
  val defExtension = "def"
  val paramPrefix = "#"
  val noOutputCheck = "nope"

  // The path starts from the project root.
  val rootDir: String = "./src/test/resources/synthesis".replace("/", File.separator)

  val synthesis: Synthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit

  import synthesis._
  
  def getDescInputOutput(testFilePath: String, initialParams: SynConfig = defaultConfig): (String, String, String, String, SynConfig) = {
    val file = new File(testFilePath)
    val format = testFilePath match{
      case s if s.endsWith(testExtension) => dotSyn
      case s if s.endsWith(sketchExtension) => dotSus
    }
    // The path is counted from the rout
    val allLines = Source.fromFile(file).getLines.toList
    val (params, lines) =
      if (allLines.nonEmpty && allLines.head.startsWith(paramPrefix)) {
        (SynthesisRunner.parseParams(allLines.head.drop(paramPrefix.length).split(' '), initialParams), allLines.tail)
      } else (initialParams, allLines)

    def parseSyn = {
      val i = lines.indexWhere(_.trim.contains(testSeparator))
      val (testDescr, _ :: specAndSrc) = lines.splitAt(i) // a::b matches head `a` and tail `b`
      val fname = removeSuffix(file.getName, s".$testExtension")
      val dirName = file.getParentFile.getName
      val description = if (testDescr.isEmpty) "Testing synthesis" else testDescr.mkString("\n").trim
      // The first part is the description
      val testName = s"$dirName/$fname"
      val desc = s"[$testName] $description"

      val j = specAndSrc.indexWhere(_.trim.startsWith(testSeparator))
      val (spec, expectedSrc) = specAndSrc.splitAt(j)
      val input = spec.mkString(" ").trim
      val output = expectedSrc.tail.mkString("\n").trim
      (testName, desc, input, output, params.copy(inputFormat = format))
    }

    def parseSus = {
      val hasDescr = lines.head.trim.startsWith("/*") // todo:support multiline descr
      val desc = if(hasDescr) lines.head.trim else ""

      val j = lines.indexWhere(_.trim.startsWith(testSeparator))
      val (spec, expectedSrc) = lines.splitAt(j)

      val input = spec.mkString(" ").trim
      val testName = testFilePath
      val output = expectedSrc.tail.mkString("\n").trim
      (testName, desc, input, output, params.copy(inputFormat = format))
    }

    format match {
      case `dotSyn` => parseSyn
      case `dotSus` => parseSus
    }
  }

  def synthesizeFromFile(dir: String, testName: String): Unit = {
    val (_, desc, in, out, params) = getDescInputOutput(testName)
    synthesizeFromSpec(testName, in, out, params)
  }

  def synthesizeFromSpec(testName: String, text: String, out: String = noOutputCheck, params: SynConfig = defaultConfig) : Unit = {
    val parser = new SSLParser
    val res = params.inputFormat match {
      case `dotSyn` => parser.parseGoalSYN(text)
      case `dotSus` => parser.parseGoalSUS(text)
    }
    if (!res.successful) {
      throw SynthesisException(s"Failed to parse the input:\n$res")
    }

    val prog = res.get
    // assert(prog.predicates.nonEmpty)
    val (specs, env, body) = resolveProgram(prog)

    if (specs.lengthCompare(1) != 0) {
      throw SynthesisException("Expected a single synthesis goal")
    }

    val spec = specs.head
    val time1 = System.currentTimeMillis()
    val sresult = synthesizeProc(spec, env.copy(config = params), body)
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
          testPrintln(s"Number of saved negative results: ${stats.numSavedResultsNegative}")
          testPrintln(s"Number of saved positive results: ${stats.numSavedResultsPositive}")
          testPrintln(s"Number of recalled negative results: ${stats.numRecalledResultsNegative}")
          testPrintln(s"Number of recalled positive results: ${stats.numRecalledResultsPositive}")
          testPrintln(result)
          testPrintln("-----------------------------------------------------")
        } else {
          println(result)
        }
        if (out != noOutputCheck) {
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
      val tests = testDir.listFiles.filter(f => f.isFile
        && (f.getName.endsWith(s".$testExtension") ||
            f.getName.endsWith(s".$sketchExtension"))).toList
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
      val tests = testDir.listFiles.filter(f => f.isFile
        && (f.getName.endsWith(s".$testExtension") ||
            f.getName.endsWith(s".$sketchExtension"))).toList
      tests.find(f => f.getName == fname) match {
        case Some(f) =>
          val (testName, desc, in, out, allParams) = getDescInputOutput(f.getAbsolutePath, params)
          val fullInput = List(defs, in).mkString("\n")
          doRun(testName, desc, fullInput, out, allParams)
        case None =>
          System.err.println(s"No file with the name $fname found in the directory $dir.")
      }
    }
  }


  def removeSuffix(s: String, suffix: String): String = {
    if (s.endsWith(suffix)) s.substring(0, s.length - suffix.length) else s
  }

}

