package org.tygus.suslik.certification.targets.htt.language

trait PrettyPrinting {
  def pp: String = toString
  def getIndent(depth: Int): String = "  " * depth
}
