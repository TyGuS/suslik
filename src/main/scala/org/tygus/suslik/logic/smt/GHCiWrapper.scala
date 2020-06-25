package org.tygus.suslik.logic.smt

import java.util.concurrent.TimeUnit

import org.bitbucket.franck44.expect.Expect

import scala.concurrent.duration.FiniteDuration
import scala.util.{Failure, Success}

/**
  *
  * An experiment with a nI/O wrapper around ghci process 
  *
  * @author Ilya Sergey
  */
object GHCiWrapper {

  // Timeout for the I/O Future
  val superLongTimeout = new FiniteDuration(10000, TimeUnit.MILLISECONDS)
  val timeout = new FiniteDuration(2000, TimeUnit.MILLISECONDS)

  // A delimiter after each token read from the output.
  val delimiter = "\n".r
  // GHCi's standard prompt. Somehow gets attached to the next answers (but consistently),
  // so needs to be trimmed away
  val prefix = "Prelude> "

  private lazy val solverProcess = startSolver()

  def main(args: Array[String]): Unit = {
    // Warm-up
    for (i <- 1 to 5) yield factorial(i + 5)

    // Real stuff
    for (i <- 1 to 20) {
      val t1 = System.currentTimeMillis()
      val result = factorial(i)
      val t2 = System.currentTimeMillis()
      println(s"Result: $result, Time: ${t2 - t1}ms")
    }

    solverProcess.destroy()
    // No longer usable, so the next line will fail
    // println(product(2, 2))
  }


  // Compute product
  def product(a: Int, b: Int): Long = {
    val command = s"$a * $b\n"
    computeIntOperation(command)
  }

  // Compute factorial
  def factorial(a: Int): Long = {
    val command = s"product [1 .. $a]\n"
    computeIntOperation(command)
  }

  // Can be used concurrently by Scala tests
  private def computeIntOperation(command: String): Long = this.synchronized {
    // Send command, then expect an answer
    solverProcess.send(command) flatMap (_ => solverProcess.expect(delimiter, timeout)) match {
      case Success(value) => value.stripPrefix(prefix).toLong
      case Failure(exception) => throw new Exception(s"Everything is broken, here's why:\n $exception")
    }
  }

  private def startSolver(): Expect = {
    disableLogging()
    val solverTerminal = Expect("ghci", Nil)
    // Ignore the initial prompt
    solverTerminal.expect(delimiter, superLongTimeout)
    solverTerminal
  }
}
