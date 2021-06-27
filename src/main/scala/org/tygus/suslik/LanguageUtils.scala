package org.tygus.suslik

/**
  * @author Ilya Sergey
  */

object LanguageUtils {

  private val init = 0

  private var now = init

  def resetFreshNameGenerator(): Unit = {
    now = init
  }
  
  val cardinalityPrefix = "_alpha_"

  def getTotallyFreshName(prefix: String): String = {
    val s = s"$prefix$now"
    now = now + 1
    s
  }

}