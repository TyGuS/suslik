package org.tygus.suslik.certification.targets.coq.language

trait ProgramPrettyPrinting extends PrettyPrinting {
  def ppp: String = this.pp
}
