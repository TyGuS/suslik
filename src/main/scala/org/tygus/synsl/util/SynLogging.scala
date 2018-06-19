package org.tygus.synsl.util

import org.tygus.synsl.language.Statements.Procedure
import org.tygus.synsl.logic.Goal
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.synthesis.SynthesisRule
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
  private var backracking: Int = 0
  private var successful: Int = 0
  private var lasting: Int = 0

  def bumpUpBacktracing() {
    backracking = backracking + 1
  }

  def bumpUpSuccessfulRuleApp() {
    successful = successful + 1
  }

  def bumpUpLastingSuccess() {
    lasting = lasting + 1
  }

  def numBack: Int = backracking
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
    List("Name", "Time", "Backtrackings", "Lasting", "Total", "SMT Cache").mkString(", ") + "\n "

  {
    if (myFile.exists()) myFile.delete()
    myFile.createNewFile()
    using(new FileWriter(myFile, true))(_.write(initRow))
  }

  def using[A <: {def close() : Unit}, B](resource: A)(f: A => B): B =
      try f(resource) finally resource.close()

  def log(name: String, time: Long, stats: Option[(Procedure, SynStats)]): Unit = {
    val statRow = (stats match {
      case Some((_, st)) => List(st.numBack, st.numLasting, st.numSucc, st.smtCacheSize)
      case None => DList.replicate(4, "FAIL").toList
    }).mkString(", ")

    val data = s"$name, $time, $statRow\n"
    using(new FileWriter(myFile, true))(_.write(data))
  }

}