package org.tygus.synsl

import org.tygus.synsl.language.Expressions.{Expr, Var}
import org.tygus.synsl.logic.Specifications.Spec

/**
  * @author Ilya Sergey
  */

trait PrettyPrinting {
  def pp : String = toString
}


trait Substitutable[A] {
  // Variable substitution
  def subst(x: Var, by: Expr) : A
}

object LanguageUtils {

  def generateFreshName(s: Spec): Var = ???

}