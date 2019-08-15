package org.tygus.suslik.language

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.MTag

/**
  * @author Ilya Sergey
  */

trait Substitutable[+A] {

  // Variable substitution
  def subst(x: Var, by: Expr) : A = {
    this.subst(Substitution(Map.empty[Var,Expr] + (x -> by), Map.empty))
  }

  def subst(substitution: Substitution) : A

  def subst(m: Map[Var, Expr]) : A = {
    this.subst(Substitution(m))
  }
}

case class Substitution(exprMapping : Map[Var, Expr] =  Map.empty[Var, Expr],
                        mutMapping: Map[Var, MTag] = Map.empty[Var, MTag]) {

  def +(v: Var, e: Expr): Substitution = {
    Substitution(exprMapping + (v -> e), mutMapping)
  }

  def +(v: Var, m: MTag) : Substitution = {
    Substitution(exprMapping, mutMapping + (v -> m))
  }

  def getOrElse(key: Var, default: Expr): Expr = {
    exprMapping.getOrElse(key, default)
  }

  def getOrElse(key: Var, default: MTag): MTag = {
    mutMapping.getOrElse(key, default)
  }
}
/*

sealed class Substitute[T] {
  object Substitute {
    implicit object MTagResult extends Substitute[MTag]
    implicit object PFResult extends Substitute[PFormula]
  }
}
*/
