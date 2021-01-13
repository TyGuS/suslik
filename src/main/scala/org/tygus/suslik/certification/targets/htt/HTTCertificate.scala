package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.targets.htt.language.Types.CNatSeqType
import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences.CFunSpec
import org.tygus.suslik.certification.targets.htt.program.Statements.CProcedure
import org.tygus.suslik.certification.targets.htt.translation.IR.PredicateEnv
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget}

case class HTTCertificate(name: String, preds: PredicateEnv, spec: CFunSpec, proof: Proof.Step, proc: CProcedure, hints: Seq[Hint.Item] = Seq.empty) extends Certificate {
  val target: CertificationTarget = HTT

  // Replace hyphens with underscores
  def sanitize(txt: String): String = txt.replace('-', '_')

  // Import Coq dependencies
  private val prelude = s"""From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

"""

  def pp: String = {
    val builder = new StringBuilder
    builder.append(prelude)
    preds.values.foreach(pred => builder.append(pred.pp + "\n"))
    builder.append(spec.pp)
    builder.append("\n")
    if (hints.nonEmpty) {
      builder.append("\n")
      builder.append(hints.map(_.pp).mkString("\n"))
      builder.append("\n\n")
    }
    builder.append(proc.pp)
    builder.append("\n")
    builder.append(proof.pp)
    builder.toString
  }

  def inferHints: HTTCertificate = {
    val predHints = preds.values.filter(p => p.params.map(_._1).contains(CNatSeqType)).map(p => Hint.PredicateSetTransitive(p)).toSeq

    this.copy(hints = predHints)
  }

  override def outputs: List[CertificateOutput] =  List(CertificateOutput(None, sanitize(name), pp))

}
