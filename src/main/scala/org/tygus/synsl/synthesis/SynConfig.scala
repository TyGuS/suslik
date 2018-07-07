package org.tygus.synsl.synthesis

import org.tygus.synsl.language.PrettyPrinting

/**
  * @author Ilya Sergey
  */

case class SynConfig(
                      // Synthesis params
                      startingDepth: Int        = 100,
                      maxOpenDepth: Int         = 1,
                      maxCloseDepth: Int        = 1,
                      branchAbduction: Boolean  = false,
                      phased: Boolean           = true,
                      invert: Boolean           = true,
                      fail: Boolean             = true,
                      commute: Boolean          = true,
                      // Timeout and logging
                      printDerivations: Boolean = true,
                      printFailed: Boolean      = false,
                      printTags: Boolean        = false,
                      assertSuccess: Boolean    = true,
                      timeOut: Long             = DEFAULT_TIMEOUT
                    ) extends PrettyPrinting {

  def combine(params: SynConfig): SynConfig =
    // TODO: properly combine elementwise
    if (params == defaultConfig) this else params

  override def pp: String =
    ( (if (maxOpenDepth == 1) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == 1) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (!branchAbduction) Nil else List(s"branchAbduction = $branchAbduction")) ++
      (if (phased) Nil else List(s"phased = $phased")) ++
      (if (invert) Nil else List(s"invert = $invert")) ++
      (if (fail) Nil else List(s"fail = $fail")) ++
      (if (commute) Nil else List(s"commute = $commute"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)


