package org.tygus.synsl

import org.tygus.synsl.language._
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.SynslType

package object logic {

  type Gamma = Seq[(SynslType, Var)]
  type PredIndex = Map[Ident, InductivePredicate]
}
