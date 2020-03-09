package org.tygus.suslik

import java.time.Instant

/**
  * @author Ilya Sergey
  */
package object parsing {

  private var now = Instant.now().getEpochSecond

  def getTotallyFreshName(): String = {
    val s = s"c$now"
    now = now + 1
    s 
  }

}
