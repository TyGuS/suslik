package org.tygus.synsl

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.logic._

/**
  * @author Ilya Sergey
  */

object LanguageUtils {

  def generateFreshVar(s: Spec, tmpName: String = "tmp"): Var = {
    var counter = 1
    var candidate = Var(s"$tmpName")
    val existing = s.vars
    while (existing.contains(candidate)) {
      counter = counter + 1
      candidate = Var(s"$tmpName$counter")
    }
    candidate
  }

}