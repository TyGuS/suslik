package org.tygus.suslik

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Specifications._

/**
  * @author Ilya Sergey
  */

object LanguageUtils {

  val tmpPrefix = "$tmp"

  def generateFreshVar(s: Goal, tmpName: String = "$tmp"): Var = {
    var counter = 1
    var candidate = Var(s"$tmpName")
    val existing = s.vars
    while (existing.contains(candidate)) {
      counter = counter + 1
      candidate = Var(s"$tmpName$counter")
    }
    candidate
  }

  def generateFreshExistential(existing: Set[Var], tmpName: String = "$ex"): Var = {
    var counter = 1
    var candidate = Var(s"$tmpName")
    while (existing.contains(candidate)) {
      counter = counter + 1
      candidate = Var(s"$tmpName$counter")
    }
    candidate
  }

  def isNotDefaultFreshVar(v: Var): Boolean = !v.name.startsWith(tmpPrefix)

}