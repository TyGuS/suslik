package org.tygus.suslik

import scala.util.DynamicVariable

/**
  * @author Ilya Sergey
  */

object LanguageUtils {

  private val init = 0

  private val now = new DynamicVariable(init)

  def resetFreshNameGenerator(): Unit = {
    now.value = init
  }
  
  val cardinalityPrefix = "_alpha_"

  def getTotallyFreshName(prefix: String): String = {
    val s = s"$prefix${now.value}"
    now.value += 1
    s
  }

}