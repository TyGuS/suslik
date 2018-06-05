package org.tygus.synsl.logic

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.configurations.SMTLogics.QF_LIA
import org.bitbucket.franck44.scalasmt.configurations.SMTOptions.MODELS
import org.bitbucket.franck44.scalasmt.interpreters.SMTSolver

/**
  * @author Ilya Sergey
  */

package object smt {

  def disableLogging()  {
      org.slf4j.LoggerFactory.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME)
          .asInstanceOf[ch.qos.logback.classic.Logger]
          .setLevel(ch.qos.logback.classic.Level.WARN)
    }

  def infoLogging()  {
      org.slf4j.LoggerFactory.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME)
          .asInstanceOf[ch.qos.logback.classic.Logger]
          .setLevel(ch.qos.logback.classic.Level.INFO)
    }

}
