package org.tygus.synsl.language

import org.tygus.synsl.language.Expressions._

/**
  * @author Ilya Sergey
  */

trait Substitutable[+A] {

  type Subst = Map[Var,Expr]
  type SubstVar = Map[Var, Var]

  // Variable substitution
  def subst(x: Var, by: Expr) : A = {
    this.subst(Map.empty[Var,Expr] + (x -> by))
  }

  def subst(sigma: Subst) : A
}
