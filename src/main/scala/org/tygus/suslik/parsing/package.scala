package org.tygus.suslik

/**
  * @author Ilya Sergey
  */
package object parsing {

  private var now = 1583756044

  def getTotallyFreshName(): String = {
    val s = s"c$now"
    now = now + 1
    s 
  }

}
