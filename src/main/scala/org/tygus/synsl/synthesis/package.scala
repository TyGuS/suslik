package org.tygus.synsl

import org.tygus.synsl.language.Statements.Statement

/**
  * @author Ilya Sergey
  */

package object synthesis {

  // A continuation for synthesizing the "larger" statement from substatement
  type StmtProducer = Seq[Statement] => Statement

  def identityProducer: StmtProducer = _.head

  val DEFAULT_TIMEOUT = 300000
  val defaultConfig : SynConfig = new SynConfig




}
