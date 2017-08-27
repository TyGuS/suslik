package org.tygus.synsl

import org.tygus.synsl.language.SynslType
import org.tygus.synsl.logic.Specifications
import org.tygus.synsl.language.Expressions

/**
  * An implementation of a rule for synthesis
  *
  * @author Ilya Sergey
  */

trait Rules {

  import Expressions._
  import Specifications._

  type Gamma = Seq[(SynslType, Var)]
  type Pre = Assertion
  type Post = Assertion



}
