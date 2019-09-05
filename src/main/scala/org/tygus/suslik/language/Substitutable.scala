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

  def ++(o: Substitution) : Substitution = {
    Substitution(exprMapping ++ o.exprMapping, mutMapping ++ o.mutMapping)
  }

  def getOrElse(key: Var, default: Expr): Expr = {
    exprMapping.getOrElse(key, default)
  }

  def getOrElse(key: Var, default: MTag): MTag = {
    mutMapping.getOrElse(key, default)
  }

  def keyset(): Set[Var] = {
    exprMapping.keySet ++ mutMapping.keySet
  }

  def noConflict(o: Substitution): Boolean = {
    exprMapping.keySet.intersect(o.mutMapping.keySet).isEmpty
  }

  def contains(x: Var): Boolean = {
    exprMapping.contains(x) || mutMapping.contains(x)
  }

  def filterNot[A](p: ((Var, Any)) => Boolean ): Substitution = { // TODO [Immutability] Any is terrible
    Substitution(exprMapping.filterNot(p), mutMapping.filterNot(p))
  }

  def sameValueAt(k: Var, o: Substitution): Boolean = {
    if (exprMapping.isDefinedAt(k)) {
      exprMapping(k) == o.exprMapping(k)
    } else if (mutMapping.isDefinedAt(k)) {
      mutMapping(k) == o.mutMapping(k)
    } else false
  }

  // TODO [Immutability] could probably abstract these generic types of operations
  // with and and or operations
  def isDefinedAt(k: Var): Boolean = {
    exprMapping.isDefinedAt(k) || mutMapping.isDefinedAt(k)
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
