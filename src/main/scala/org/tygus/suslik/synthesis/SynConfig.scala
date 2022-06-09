package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.certification.CertificationTarget.NoCert
import org.tygus.suslik.language.PrettyPrinting

import scala.concurrent.duration.Deadline

/**
  * @author Ilya Sergey
  */

sealed trait InputFormat
case object dotSyn extends InputFormat
case object dotSus extends InputFormat

case class SynConfig(
                      // Synthesis params
                      maxOpenDepth: Int = 1,
                      maxCloseDepth: Int = 1,
                      maxCalls: Int = 2,
                      auxAbduction: Boolean = true,
                      branchAbduction: Boolean = false,
                      maxGuardConjuncts: Int = 2,
                      depthFirst: Boolean = false,
                      breadthFirst: Boolean = false,
                      memoization: Boolean = true,
                      delegatePure: Boolean = false,
                      extendedPure: Boolean = false,
                      simple: Boolean = false,
                      // Timeout and logging
                      interactive: Boolean = false,
                      printStats: Boolean = false,
                      printSpecs: Boolean = true,
                      traceLevel: Int = 0,
                      assertSuccess: Boolean = false,
                      logToFile: Boolean = true,
                      traceToJsonFile: Option[File] = None,
                      timeOut: Long = 1800000, // milliseconds
                      // Certification
                      certTarget: CertificationTarget = NoCert,
                      certDest: File = null,
                      certHammerPure: Boolean = false,
                      certSetRepr: Boolean = false,
                      // Internal (not directly settable through CLI)
                      inputFormat: InputFormat = dotSyn,
                      script: List[Int] = List()
                    ) extends PrettyPrinting {

  override def pp: String =
    ((if (maxOpenDepth == defaultConfig.maxOpenDepth) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == defaultConfig.maxCloseDepth) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (auxAbduction == defaultConfig.auxAbduction) Nil else List(s"auxAbduction = $auxAbduction")) ++
      (if (branchAbduction == defaultConfig.branchAbduction) Nil else List(s"branchAbduction = $branchAbduction")) ++
      (if (depthFirst == defaultConfig.depthFirst) Nil else List(s"depthFirst = $depthFirst")) ++
      (if (memoization == defaultConfig.memoization) Nil else List(s"memoization = $memoization")) ++
      (if (certTarget == defaultConfig.certTarget) Nil else List(s"certTarget = ${certTarget.name}")) ++
      (if (certDest == defaultConfig.certDest) Nil else List(s"certDest = ${certDest.getCanonicalPath}")) ++
      (if (certHammerPure == defaultConfig.certHammerPure) Nil else List(s"certHammerPure = $certHammerPure")) ++
      (if (certSetRepr == defaultConfig.certSetRepr) Nil else List(s"certSetRepr = $certSetRepr"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)

case class SymbolicExecutionError(msg: String) extends Exception(msg)


