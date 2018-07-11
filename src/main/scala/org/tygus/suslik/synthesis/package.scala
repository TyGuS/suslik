package org.tygus.suslik

import org.tygus.suslik.language.Statements.Statement

/**
  * @author Ilya Sergey
  */

package object synthesis {

  // A continuation for synthesizing the "larger" statement from substatement
  type StmtProducer = Seq[Statement] => Statement


  val DEFAULT_TIMEOUT = 120000
  val defaultConfig : SynConfig = new SynConfig
}
