package org.tygus.synsl

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.language.SynslType
import org.tygus.synsl.logic.Specifications._

/**
  * @author Ilya Sergey
  */

object Synthesis {

  type Gamma = Seq[(SynslType, Var)]

  def synthesize(spec: Spec): Procedure = {

    // TODO: implement Nadia's rules
    ???

  }

}
