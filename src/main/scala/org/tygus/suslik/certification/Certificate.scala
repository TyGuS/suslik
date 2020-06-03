package org.tygus.suslik.certification

trait Certificate {
  val body: String
  val name: String
  val suffix: String
  def fileName: String = name + suffix
}
