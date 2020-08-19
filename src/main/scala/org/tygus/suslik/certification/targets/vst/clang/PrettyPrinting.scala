package org.tygus.suslik.certification.targets.vst.clang

trait PrettyPrinting {
  def pp: String = toString
  def ppIndent(depth: Int) = s"${getIndent(depth)}${pp.replaceAll("\n", s"\n${getIndent(depth)}")}"
  def getIndent(depth: Int): String = "  " * depth
}
