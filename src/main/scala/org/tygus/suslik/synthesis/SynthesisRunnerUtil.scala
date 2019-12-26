package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.logic.Resolver._
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.synthesis.SearchTree.AndNode
import org.tygus.suslik.util.{SynLogLevels, SynLogging, SynStatUtil, SynStats}

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
      val hasDescr = lines.head.trim.startsWith("/*") // todo:support multiline descriptions
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
    val config = params.copy(startTime = time1)
    val sresult = synthesizeProc(spec, env.copy(config = config), body)
    val time2 = System.currentTimeMillis()
    val delta = time2 - time1

    SynStatUtil.log(testName, delta, params, spec, sresult._1, sresult._2)

    def printHotNode(hotNode: AndNode, descs: Int): String =
      s"${hotNode.rule.toString} ${hotNode.consume.pp} at depth ${hotNode.parent.depth} with ${descs} descendants expanded"

    def printStats(stats: SynStats) = {
      testPrintln(s"Goals generated: ${stats.numGoalsGenerated}")
      testPrintln(s"Goals expanded: ${stats.numGoalsExpanded}")
      testPrintln(s"And-nodes backtracked: ${stats.numGoalsFailed}")
      testPrintln(s"Maximum worklist size: ${stats.maxWorklistSize}")
      testPrintln(s"Maximum goal depth: ${stats.maxGoalDepth}")
      testPrintln(s"Final size of SMT cache: ${stats.smtCacheSize}")
      val hotNodesString = stats.hotNodes(5).map{case (n, s) => printHotNode(n, s)}.mkString("\n")
      testPrintln(s"Hot nodes:\n $hotNodesString")
      val hotFNodesString = stats.hotFilteredNodes(5).map{case (n, s) => printHotNode(n.parent.get, s)}.mkString("\n")
      testPrintln(s"Hot filtered nodes:\n $hotFNodesString")
    }

    sresult._1 match {
      case Nil =>
        printStats(sresult._2)
        throw SynthesisException(s"Failed to synthesise:\n$sresult")
      case procs =>
        val result = procs.map(_.pp).mkString
        if (params.printStats) {
          testPrintln(s"\n[$testName]:", Console.MAGENTA)
          testPrintln(params.pp)
          testPrintln(s"${spec.pp}\n", Console.BLUE)
          testPrintln(s"Successfully synthesised in $delta milliseconds:", Console.GREEN)
          printStats(sresult._2)
          testPrintln(result)
          testPrintln("-----------------------------------------------------")
        } else {
          println(result)
        }
        if (out != noOutputCheck) {
          val tt = out.trim.lines.map(_.trim).toList
          val res = result.trim.lines.toList.map(_.trim)
          if (params.assertSuccess && res != tt) {
            throw SynthesisException(s"\nThe expected output\n$tt\ndoesn't match the result:\n$res")
          }
        }
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

