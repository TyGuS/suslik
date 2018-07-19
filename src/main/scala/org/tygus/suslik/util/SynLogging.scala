package org.tygus.suslik.util

import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.FunSpec
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.{SynConfig, SynthesisRule}
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
  private var successful: Int = 0
  private var lasting: Int = 0

  def bumpUpBacktracing() {
    backtracking = backtracking + 1
  }

  def bumpUpSuccessfulRuleApp() {
    successful = successful + 1
  }

  def bumpUpLastingSuccess() {
    lasting = lasting + 1
  }

  def numBack: Int = backtracking
  def numSucc : Int = successful
  def numLasting : Int = lasting
  def smtCacheSize: Int = SMTSolving.cacheSize
}

abstract sealed class SynCertificate
case class SynAxiom(goal: Goal, rule: SynthesisRule) extends SynCertificate
case class SynTree(subgoals: Seq[SynCertificate]) extends SynCertificate

// TODO: refactor me to make more customizable
object SynStatUtil {

  import java.io.{File, FileWriter}

  val myStats = "stats.csv"
  val myFile = new File(myStats)
  val initRow: String =
    List("Name", "Time", "Spec Size", "Code Size", "Backtrackings", "Lasting", "Total", "SMT Cache").mkString(", ") + "\n"

  def init(config: SynConfig){
    if (config.logToFile) {
      if (myFile.exists()) myFile.delete()
      myFile.createNewFile()
      using(new FileWriter(myFile, true))(_.write(initRow))
    }
  }

  def using[A <: {def close() : Unit}, B](resource: A)(f: A => B): B =
      try f(resource) finally resource.close()

  def log(name: String, time: Long, config: SynConfig, spec: FunSpec, stats: Option[(Procedure, SynStats)]): Unit = {
    if (config.logToFile) {
      val statRow = (stats match {
        case Some((proc, st)) => List(proc.body.size, st.numBack, st.numLasting, st.numSucc, st.smtCacheSize)
        case None => DList.replicate(4, "FAIL").toList
      }).mkString(", ")

      val specSize = spec.pre.size + spec.post.size
      val data = s"$name, $time, $specSize, $statRow, ${config.pp}\n"
      using(new FileWriter(myFile, true))(_.write(data))
    }
  }

}