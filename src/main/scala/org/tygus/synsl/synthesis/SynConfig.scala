package org.tygus.synsl.synthesis

import scala.Console.RED

/**
  * @author Ilya Sergey
  */

case class SynConfig(printDerivations: Boolean = true, assertSuccess: Boolean = true,
                     timeOut: Long = DEFAULT_TIMEOUT)

case class SynTimeOutException(msg: String) extends Exception(msg)
