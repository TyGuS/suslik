package org.tygus.suslik.language

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Gamma

/**
  * @author Ilya Sergey
  */

trait HasExpressions[+A] {

  // Variable substitution
  def subst(x: Var, by: Expr) : A = {
    this.subst(Map(x -> by))
  }

  def subst(sigma: Map[Var, Expr]) : A

  def resolveOverloading(gamma: Gamma): A

  def collect[R <: Expr](p: Expr => Boolean): Set[R]

  def vars: Set[Var] = collect(_.isInstanceOf[Var])
}
