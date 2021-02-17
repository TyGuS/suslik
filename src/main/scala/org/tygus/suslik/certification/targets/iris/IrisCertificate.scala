package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HFunDef
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget}

case class IrisCertificate(name: String, funDef: HFunDef) extends Certificate {
  val target: CertificationTarget = Iris

  private val prelude =
    s"""From iris.program_logic Require Export weakestpre.
       |From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
       |From iris.heap_lang Require Import lang notation proofmode.
       |From Hammer Require Import Hammer.
       |Context `{!heapG Σ}.
       |Context {PROP : bi}.
       |Implicit Types Δ : envs PROP.
       |Set Default Proof Using "Type".
       |
       |""".stripMargin

  def pp : String = {
    val b = new StringBuilder
    b.append(prelude)
    b.append(funDef.pp)
    b.toString()
  }

  override def outputs: List[CertificateOutput] =  List(CertificateOutput(None, name, pp))
}
