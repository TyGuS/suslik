package org.tygus.synsl.util

/**
  * @author Ilya Sergey
  */

object StringUtil {

  def mkSpaces(n: Int) : String = (for (i <- 0 until n) yield " ").mkString("")

}
