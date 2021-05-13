package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CFunSpec, CInductivePredicate}
import org.tygus.suslik.certification.targets.htt.program.Program
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CoqOutput}

case class HTTCertificate(name: String, predicates: List[CInductivePredicate], spec: CFunSpec, auxSpecs: Seq[CFunSpec], proof: Proof, proc: Program, hints: Seq[Hint] = Seq.empty) extends Certificate[HTT, CInductivePredicate] {
  // Replace hyphens with underscores
  def sanitize(txt: String): String = txt.replace('-', '_')

  def pp: String =
    s"""${HTT.prelude}
       |${predicates.map(_.pp).mkString("\n\n")}
       |$ppMain
       |""".stripMargin

  def ppExternalDefs: String = s"${HTT.prelude}\nRequire Import common.\n\n$ppMain"

  private def ppMain: String = {
    val builder = new StringBuilder

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

  override def outputs: List[CertificateOutput] =  List(CoqOutput(s"${sanitize(name)}.v", sanitize(name), ppExternalDefs))

}