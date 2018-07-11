package org.tygus.suslik

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._

package object logic {

  type Formals = List[(SSLType, Var)]
  type PredicateEnv = Map[Ident, InductivePredicate]
  type FunctionEnv = Map[Ident, FunSpec]
  type Gamma =  Map[Var, SSLType]
}
