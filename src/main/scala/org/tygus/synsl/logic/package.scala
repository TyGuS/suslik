package org.tygus.synsl

import org.tygus.synsl.language._
import org.tygus.synsl.language.Expressions._

package object logic {

  type Formals = List[(SynslType, Var)]
  type PredicateEnv = Map[Ident, InductivePredicate]
  type FunctionEnv = Map[Ident, FunSpec]
  type Gamma =  Map[Var, SynslType]
}
