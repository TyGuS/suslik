package org.tygus.suslik.util

import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.FunSpec
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.{SynConfig}
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import scalaz.DList

/**
  * @author Ilya Sergey
  */

sealed abstract class SynLogging {
  def print(s: String): Unit

  def println(s: String): Unit

  def println(): Unit

  def printlnErr(s: String): Unit

  def testPrintln(s: String, color: String = Console.BLACK): Unit
}

/**
  * Different loggind levels
  */
object SynLogLevels {

  object Verbose extends SynLogging {
    override def printlnErr(s: String): Unit = System.err.println(s)

    override def print(s: String): Unit = Console.print(s)

    override def println(s: String): Unit = Console.println(s)

    override def testPrintln(s: String, color: String = Console.BLACK): Unit = {
      Console.println(s"$color$s${Console.BLACK}")
    }

    override def println(): Unit = Console.println()
  }

  object Test extends SynLogging {
    // Mute standard print
    override def println(s: String): Unit = {}

    override def print(s: String): Unit = {}

    override def println(): Unit = {}

    override def printlnErr(s: String): Unit = Console.println(s)

    override def testPrintln(s: String, color: String = Console.BLACK): Unit = {
      Console.println(s"$color$s${Console.BLACK}")
    }
  }

}

class SynStats {
  private var backtracking: Int = 0
  private var ruleApps: Int = 0
  private var maxWLSize: Int = 0
  private var maxDepth: Int = 0

  def bumpUpBacktracing() {
    backtracking = backtracking + 1
  }

  def bumpUpRuleApps() {
    ruleApps = ruleApps + 1
  }

  def updateMaxWLSize(sz: Int): Unit = {
    maxWLSize = maxWLSize.max(sz)
  }

  def updateMaxDepth(d: Int): Unit = {
    maxDepth = maxDepth.max(d)
  }

  def numBack: Int = backtracking
  def numApps : Int = ruleApps
  def maxWorklistSize: Int = maxWLSize
  def maxGoalDepth: Int = maxDepth
  def smtCacheSize: Int = SMTSolving.cacheSize
}

// TODO: refactor me to make more customizable
object SynStatUtil {

  import java.io.{File, FileWriter}

  val myStats = "stats.csv"
  val myFile = new File(myStats)
  val initRow: String =
    List("Name", "Time", "Spec Size", "Code Size", "Backtrackings", "Applications", "Max Worklist Size", "SMT Cache").mkString(", ") + "\n"

  def init(config: SynConfig){
    if (config.logToFile) {
      if (myFile.exists()) myFile.delete()
      myFile.createNewFile()
      using(new FileWriter(myFile, true))(_.write(initRow))
    }
  }

  def using[A <: {def close() : Unit}, B](resource: A)(f: A => B): B =
      try f(resource) finally resource.close()

  def log(name: String, time: Long, config: SynConfig, spec: FunSpec, stats: Option[(List[Procedure], SynStats)]): Unit = {
    if (config.logToFile) {
      val statRow = (stats match {
        case Some((procs, st)) => List(procs.map(_.body.size).sum, st.numBack, st.numApps, st.maxWorklistSize, st.smtCacheSize)
        case None => DList.replicate(5, "FAIL").toList
      }).mkString(", ")

      val specSize = spec.pre.size + spec.post.size
      val data = s"$name, $time, $specSize, $statRow, ${config.pp}\n"
      using(new FileWriter(myFile, true))(_.write(data))
    }
  }

}