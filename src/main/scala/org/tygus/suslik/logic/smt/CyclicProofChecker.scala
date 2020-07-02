package org.tygus.suslik.logic.smt

import java.io.IOException
import java.util.concurrent.TimeUnit

import org.bitbucket.franck44.expect.Expect
import org.tygus.suslik.report.LazyTiming
import org.tygus.suslik.synthesis.SynthesisException

import scala.concurrent.duration.FiniteDuration
import scala.sys.process._
import scala.util.{Failure, Success}

/**
  * A wrapper around Reuben Rowe's checker for cyclic proofs
  *
  * @author Ilya Sergey
  */
object CyclicProofChecker extends LazyTiming {

  // Command, should be in your PATH
  val checkerCommand = "checkproof"

  // If we are on windows, invoke checkproof inside wsl
  lazy val useWSL = sys.props.get("os.name").get.toLowerCase.startsWith("windows")

  // A delimiter after each token read from the output.
  val delimiter = "\n".r

  // Timeout for the I/O Future
  val superLongTimeout = new FiniteDuration(5000, TimeUnit.MILLISECONDS)
  val timeout = new FiniteDuration(1000, TimeUnit.MILLISECONDS)

  override val watchName = "CyclicProofChecker"

  private var checker: Expect = null

  // Start the checker
  {
    if (isConfigured()) {
      checker = startChecker()
    }
  }

  private var warm = false
  private var configured = false

  def isConfigured(): Boolean = this.synchronized {
    configured = try {
      val result = if (useWSL) s"wsl which $checkerCommand".!! else s"which $checkerCommand".!!
      result.trim.nonEmpty
    } catch {
      case _: Throwable => false
    }
    configured
  }


  // Check cyclic proof
  def checkProof(trace: String): Boolean = this.synchronized {
    timed {
      if (!configured) {
        // [Termination] This is an unsound default
        return true
      }

      computeResultOperation(trace) match {
        case Left("YES") => true
        case Left("NO") => false
        case Right(_: IOException) => {
          // The checker broke at the previous iteration, just restart it
          checker = startChecker()
          checkProof(trace)
        }
        case z => throw SynthesisException(s"Cyclic Proof Checker error: $z\nTrace:\n$trace\n\n")
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////
  // Private methods
  /////////////////////////////////////////////////////////////////////////

  // Can be used concurrently by Scala tests
  private def computeResultOperation(command: String): Either[String, Throwable] = {
    //    if (!warm) {
    //      warm = true
    //      warmUp()
    //    }

    // Send command, then expect an answer
    checker.send(command) flatMap (_ => checker.expect(delimiter, timeout)) match {
      case Success(value) => Left(value)
      case Failure(exception) => Right(exception)
    }
  }


  private def startChecker(): Expect = {
    disableLogging()
    val checkerREPL = if (useWSL) Expect("wsl", List(checkerCommand)) else Expect(checkerCommand, Nil)
    if (!useWSL && !sys.env.isDefinedAt("TERM")) {
      checkerREPL.expect(delimiter, superLongTimeout)
    }
    checkerREPL
  }

  private def warmUp(): Unit = {
    val yesResult = checkProof(yesQuery)
    assert(yesResult)

    val noResult = checkProof(noQuery)
    assert(!noResult)
  }

  private val yesQuery =
    """
      |0 -> 0-0.0 : {}, {(a, a)}
      |0 -> 0-1.0 : {(a, zx)}, {(a, a)}
      |0-1.0 -> 0-1.1 : {(a, zx)}, {(zx, zx), (a, a)}
      |0-1.1 -> 0-1.1-0.0 : {(a, zx)}, {(zx, zx), (a, a)}
      |0-1.1 -> 0-1.1-1.0 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a)}
      |0-1.1-0.0 -> 0-1.1-0.1 : {(a, zx)}, {(zx, zx), (a, a)}
      |0-1.1-1.0 -> 0-1.1-1.1 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.1 -> 0-1.1-1.2 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.2 -> 0-1.1-1.3 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.3 -> 0-1.1-1.4 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.4 -> 0 : {}, {(ybx2, a)}
      |0-1.1-1.4 -> 0-1.1-1.5 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.5 -> 0-1.1-1.5-0.0 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.5 -> 0-1.1-1.5-1.0 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.5-1.0 -> 0-1.0 : {}, {(zbx2, zx), (a, a)}
      |0-1.1-1.5-1.0 -> 0-1.1-1.5-1.1 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)};
    """.stripMargin

  private val noQuery =
    """
      |0 -> 0-0.0 : {}, {(a, a)}
      |0 -> 0-1.0 : {(a, zx)}, {(a, a)}
      |0-1.0 -> 0-1.1 : {(a, zx)}, {(zx, zx), (a, a)}
      |0-1.1 -> 0-1.1-0.0 : {(a, zx)}, {(zx, zx), (a, a)}
      |0-1.1 -> 0-1.1-1.0 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a)}
      |0-1.1-0.0 -> 0-1.1-0.1 : {(a, zx)}, {(zx, zx), (a, a)}
      |0-1.1-1.0 -> 0-1.1-1.1 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.1 -> 0-1.1-1.2 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.2 -> 0-1.1-1.3 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.3 -> 0-1.1-1.4 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.4 -> 0 : {}, {(ybx2, a)}
      |0-1.1-1.4 -> 0-1.1-1.5 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.5 -> 0-1.1-1.5-0.0 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.5 -> 0-1.1-1.5-1.0 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)}
      |0-1.1-1.5-1.0 -> 0-1.0 : {(a, zx)}, {}
      |0-1.1-1.5-1.0 -> 0-1.1-1.5-1.1 : {(zx, ybx2), (zx, zbx2), (a, zx)}, {(zx, zx), (a, a), (zbx2, zbx2), (ybx2, ybx2)};
    """.stripMargin

}
