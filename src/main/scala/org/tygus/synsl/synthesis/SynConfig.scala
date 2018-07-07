package org.tygus.synsl.synthesis

import org.tygus.synsl.language.PrettyPrinting

/**
  * @author Ilya Sergey
  */

case class SynConfig(
                      // Synthesis params
                      startingDepth: Int              = 100,
                      maxOpenDepth: Int               = 1,
                      maxCloseDepth: Int              = 1,
                      branchAbductionEnabled: Boolean = false,
                      phasesEnabled: Boolean          = true,
                      invertibleEnabled: Boolean      = true,
                      failRulesEnabled: Boolean       = true,
                      commuteEnabled: Boolean         = true,
                      // Timeout and logging
                      printDerivations: Boolean       = true,
                      printFailed: Boolean            = false,
                      printTags: Boolean              = false,
                      assertSuccess: Boolean          = true,
                      timeOut: Long                   = DEFAULT_TIMEOUT
                    ) extends PrettyPrinting {

  def combine(params: SynConfig): SynConfig =
    // TODO: properly combine elementwise
    if (params == defaultConfig) this else params

  override def pp: String =
    ( (if (maxOpenDepth == 1) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == 1) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (!branchAbductionEnabled) Nil else List(s"branchAbductionEnabled = $branchAbductionEnabled")) ++
      (if (phasesEnabled) Nil else List(s"phasesEnabled = $phasesEnabled")) ++
      (if (invertibleEnabled) Nil else List(s"invertibleEnabled = $invertibleEnabled")) ++
      (if (failRulesEnabled) Nil else List(s"failRulesEnabled = $failRulesEnabled")) ++
      (if (commuteEnabled) Nil else List(s"commuteEnabled = $commuteEnabled"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)


