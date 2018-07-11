package org.tygus.suslik.language

import org.tygus.suslik.language.Expressions._

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
