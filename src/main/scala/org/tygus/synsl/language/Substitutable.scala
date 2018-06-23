package org.tygus.synsl.language

import org.tygus.synsl.language.Expressions._

/**
  * @author Ilya Sergey
  */

trait Substitutable[+A] {

  // Variable substitution
  def subst(x: Var, by: Expr) : A = {
    this.subst(Map.empty[Var,Expr] + (x -> by))
  }

  def subst(sigma: Map[Var, Expr]) : A
}
