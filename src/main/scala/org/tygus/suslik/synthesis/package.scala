package org.tygus.suslik

import org.tygus.suslik.language.Statements.{Solution, Statement}

/**
  * @author Ilya Sergey
  */

package object synthesis {

  type Kont = Seq[Solution] => Solution

  val defaultConfig : SynConfig = new SynConfig
}
