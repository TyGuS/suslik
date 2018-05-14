package org.tygus.synsl.util

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