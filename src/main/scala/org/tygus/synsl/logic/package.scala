package org.tygus.synsl

import org.tygus.synsl.language._
import org.tygus.synsl.language.Expressions._

package object logic {

  type Formals = List[(SynslType, Var)]
  type PredicateEnv = Map[Ident, InductivePredicate]
  type FunctionEnv = Map[Ident, FunSpec]

  // Type environment: maps variables to types
  // and keeps track of which variables are program-level, universal ghost, and existential ghost
  case class Gamma(types: Map[Var, SynslType], programVars: List[Var], existsVars: Set[Var] = Set.empty)
    extends PrettyPrinting
  {
    def this(formals: Formals) {
      this(formals.map({case (t, v) => (v, t)}).toMap, formals.map(_._2))
    }

    def toFormals: Formals = programVars.map(v => (types(v), v))

    def vars: Set[Var] = types.keySet
    def universalVars: Set[Var] = vars -- programVars -- existsVars

    def addProgramVar(v: Var, t: SynslType): Gamma = {
      Gamma(types + (v -> t), v :: programVars, existsVars)
    }

    override def pp: String = s"${programVars.map { v => s"${types(v).pp} ${v.pp}" }.mkString(", ")}"
  }

//  def fromFormals(formals: Formals): Gamma = {
//    Gamma(formals.map({case (t, v) => (v, t)}).toMap, formals.map(_._2).toSet)
//  }
}
