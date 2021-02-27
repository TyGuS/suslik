package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CFunSpec, CInductivePredicate}
import org.tygus.suslik.certification.targets.htt.program.Program
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget, CoqOutput}

case class HTTCertificate(name: String, predicates: List[CInductivePredicate], spec: CFunSpec, auxSpecs: Seq[CFunSpec], proof: Proof, proc: Program, hints: Seq[Hint] = Seq.empty) extends Certificate {
  val target: CertificationTarget = HTT

  // Replace hyphens with underscores
  def sanitize(txt: String): String = txt.replace('-', '_')

  def pp: String = {
    val builder = new StringBuilder
    builder.append(HTT.prelude)
    builder.append("Load common.\n\n")

    if (hints.nonEmpty) {
      builder.append(hints.map(_.pp).mkString("\n"))
      builder.append("\n\n")
    }

    for (spec <- auxSpecs) {
      builder.append(spec.pp)
      builder.append(s"\n\nVariable ${spec.name} : ${spec.name}_type.\n\n")
    }

    builder.append(spec.pp)
    builder.append("\n\n")

    builder.append(proc.pp)
    builder.append("\n")
    builder.append(proof.pp)
    builder.toString
  }

  override def outputs: List[CertificateOutput] =  List(CoqOutput(s"${sanitize(name)}.v", sanitize(name), pp))

}
