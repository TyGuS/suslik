package org.tygus.suslik.synthesis

import org.tygus.suslik.language.PrettyPrinting

/**
  * @author Ilya Sergey
  */

sealed trait InputFormat
case object dotSyn extends InputFormat
case object dotSus extends InputFormat

case class SynConfig(
                      // Synthesis params
                      maxOpenDepth: Int         = 1,
                      maxCloseDepth: Int        = 1,
                      auxAbduction: Boolean     = false,
                      branchAbduction: Boolean  = false,
                      phased: Boolean           = true,
                      invert: Boolean           = true,
                      fail: Boolean             = true,
                      commute: Boolean          = true,
                      depthFirst: Boolean       = true,
                      // Timeout and logging
                      printStats: Boolean       = true,
                      printDerivations: Boolean = false,
                      printFailed: Boolean      = false,
                      printTags: Boolean        = false,
                      printEnv: Boolean         = false,
                      assertSuccess: Boolean    = false, // true,
                      logToFile: Boolean        = true,
                      memoization: Boolean      = true,
                      timeOut: Long             = 120000,
                      inputFormat: InputFormat = dotSyn,
                      // Global state
                      startTime: Long           = 0
                    ) extends PrettyPrinting {

  override def pp: String =
    ( (if (maxOpenDepth == defaultConfig.maxOpenDepth) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == defaultConfig.maxCloseDepth) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (auxAbduction == defaultConfig.auxAbduction) Nil else List(s"auxAbduction = $auxAbduction")) ++
      (if (branchAbduction == defaultConfig.branchAbduction) Nil else List(s"branchAbduction = $branchAbduction")) ++
      (if (phased == defaultConfig.phased) Nil else List(s"phased = $phased")) ++
      (if (invert == defaultConfig.invert) Nil else List(s"invert = $invert")) ++
      (if (fail == defaultConfig.fail) Nil else List(s"fail = $fail")) ++
      (if (commute == defaultConfig.commute) Nil else List(s"commute = $commute"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)
case class SymbolicExecutionError(msg: String) extends Exception(msg)


