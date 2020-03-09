package org.tygus.suslik

/**
  * @author Ilya Sergey
  */
package object parsing {
  
  private val init= 239932

  private var now = init
  
  def resetFreshNameGenerator(): Unit = {
    now = init
  }

  def getTotallyFreshName(): String = {
    val s = s"c$now"
    now = now + 1
    s
  }

}
