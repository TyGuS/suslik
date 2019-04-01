package org.tygus.suslik.util

/**
  * @author Ilya Sergey
  */

object StringUtil {

  def mkSpaces(n: Int) : String = (for (i <- 0 until n) yield " ").mkString("")

  def withOffset(text:String, offset: Int):String = {
    mkSpaces(offset) + text.replace("\n", "\n" + mkSpaces(offset))
  }

}
