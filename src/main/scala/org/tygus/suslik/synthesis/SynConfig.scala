package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.language.PrettyPrinting

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
                      depthFirst: Boolean = false,
                      breadthFirst: Boolean = false,
                      memoization: Boolean = true,
                      termination: TerminationMetric = lexicographic,
                      delegatePure: Boolean = true,
                      // Timeout and logging
                      interactive: Boolean = false,
                      printStats: Boolean = true,
                      printSpecs: Boolean = false,
                      printDerivations: Boolean = false,
                      printFailed: Boolean = false,
                      printEnv: Boolean = false,
                      printColor: Boolean = true,
                      assertSuccess: Boolean = false,
                      logToFile: Boolean = true,
                      traceToJsonFile: Option[File] = None,
                      timeOut: Long = 120000,
                      // Certification
                      certTarget: CertificationTarget = null,
                      certDest: File = null,
                      // Internal (not directly settable through CLI)
                      inputFormat: InputFormat = dotSyn,
                      script: List[Int] = List()
                    ) extends PrettyPrinting {

  override def pp: String =
    ((if (maxOpenDepth == defaultConfig.maxOpenDepth) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == defaultConfig.maxCloseDepth) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (auxAbduction == defaultConfig.auxAbduction) Nil else List(s"auxAbduction = $auxAbduction")) ++
      (if (branchAbduction == defaultConfig.branchAbduction) Nil else List(s"branchAbduction = $branchAbduction")) ++
      (if (phased == defaultConfig.phased) Nil else List(s"phased = $phased")) ++
      (if (depthFirst == defaultConfig.depthFirst) Nil else List(s"depthFirst = $depthFirst")) ++
      (if (memoization == defaultConfig.memoization) Nil else List(s"memoization = $memoization")) ++
      (if (certTarget == defaultConfig.certTarget) Nil else List(s"certTarget = ${certTarget.name}")) ++
      (if (certDest == defaultConfig.certDest) Nil else List(s"certDest = ${certDest.getCanonicalPath}"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)

case class SymbolicExecutionError(msg: String) extends Exception(msg)


