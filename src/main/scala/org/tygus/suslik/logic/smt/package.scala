package org.tygus.suslik.logic

/**
  * @author Ilya Sergey
  */

package object smt {

  val LOGGER_NAMES = List("org.bitbucket.franck44", "smt2",
    "org.tygus.suslik.logic.smt", "class org.tygus.suslik.logic.smt")

  def disableLogging()  {
    for (name <- LOGGER_NAMES)
      org.slf4j.LoggerFactory.getLogger(name)
          .asInstanceOf[ch.qos.logback.classic.Logger]
          .setLevel(ch.qos.logback.classic.Level.WARN)
  }

  def infoLogging()  {
    for (name <- LOGGER_NAMES)
      org.slf4j.LoggerFactory.getLogger(name)
          .asInstanceOf[ch.qos.logback.classic.Logger]
          .setLevel(ch.qos.logback.classic.Level.INFO)
  }

}
