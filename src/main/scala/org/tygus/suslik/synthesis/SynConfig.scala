package org.tygus.suslik.synthesis

import java.io.File
import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.language.PrettyPrinting

import scala.collection.mutable.ArrayBuffer

/**
 * @author Ilya Sergey
 */

sealed trait InputFormat
case object dotSyn extends InputFormat
case object dotSus extends InputFormat

sealed trait TerminationMetric
case object totalSize extends TerminationMetric
case object lexicographic extends TerminationMetric

case class SynConfig(
                      // Synthesis params
                      maxOpenDepth: Int = 1,
                      maxCloseDepth: Int = 1,
                      maxCalls: Int = 2,
                      auxAbduction: Boolean = true,
                      branchAbduction: Boolean = false,
                      maxGuardConjuncts: Int = 2,
                      phased: Boolean = true,
                      invert: Boolean = true,
                      fail: Boolean = true,
                      commute: Boolean = false,
                      depthFirst: Boolean = false,
                      breadthFirst: Boolean = false,
                      memoization: Boolean = true,
                      delegatePure: Boolean = false,
                      extendedPure: Boolean = false,
                      // Timeout and logging
                      interactive: Boolean = false,
                      printStats: Boolean = true,
                      printSpecs: Boolean = false,
                      printDerivations: Boolean = false,
                      printFailed: Boolean = false,
                      printTags: Boolean = false,
                      printEnv: Boolean = false,
                      assertSuccess: Boolean = false,
                      logToFile: Boolean = true,
                      logFile: String = "",
                      traceToJsonFile: Option[File] = None,
                      timeOut: Long = 1800000,
                      // Certification
                      certTarget: CertificationTarget = null,
                      certDest: File = null,
                      // Internal (not directly settable through CLI)
                      inputFormat: InputFormat = dotSyn,
                      script: List[Int] = List(),
                      // Global state
                      startTime: Long = 0,
                      // genetic algorithm to improve rule orderings.
                      evolutionary: Boolean = false,
                      groupID: Int = 0,
                      generationID: Int = 0,
                      individualID: Int = 0,
                      //orderOfAnyPhaseRuless: ArrayBuffer[ArrayBuffer[Int]] = ArrayBuffer[ArrayBuffer[Int]](),
                      /**
                       * [EVALUATION] these dummy `flags` are solely used for the evaluation purposes.
                       * By default they have no meaning, but one can use them to turn on/off some
                       * feature of choice. If more flags are needed, simply add more elements to
                       * the flags list below.
                       *
                       * IMPORTANT: remember to remove the flags check from the scala code once done
                       * with the evaluation, to make sure it does not interfere with future evaluations.
                       */
                      flags: List[Boolean]      = (1 to 18).toList.map( _ => false),
                    ) extends PrettyPrinting {

  override def pp: String =
    ((if (maxOpenDepth == defaultConfig.maxOpenDepth) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == defaultConfig.maxCloseDepth) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (auxAbduction == defaultConfig.auxAbduction) Nil else List(s"auxAbduction = $auxAbduction")) ++
      (if (branchAbduction == defaultConfig.branchAbduction) Nil else List(s"branchAbduction = $branchAbduction")) ++
      (if (depthFirst == defaultConfig.depthFirst) Nil else List(s"depthFirst = $depthFirst")) ++
      (if (memoization == defaultConfig.memoization) Nil else List(s"memoization = $memoization")) ++
      (if (certTarget == defaultConfig.certTarget) Nil else List(s"certTarget = ${certTarget.name}")) ++
      (if (certDest == defaultConfig.certDest) Nil else List(s"certDest = ${certDest.getCanonicalPath}"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)

case class SymbolicExecutionError(msg: String) extends Exception(msg)


