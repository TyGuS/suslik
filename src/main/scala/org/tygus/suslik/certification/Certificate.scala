package org.tygus.suslik.certification

abstract class Certificate {
  val body: String
  val name: String
  val suffix: String
  def fileName: String = name + suffix
}
