package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HFunDef
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{IFunSpec, IPredicate}
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget, CoqOutput}

case class IrisCertificate(name: String, predicates: List[IPredicate], funDef: HFunDef, helperSpecs: List[IFunSpec], funSpec: IFunSpec, proofStr: String) extends Certificate[Iris, IPredicate] {
  val target: CertificationTarget = Iris()

  private val prelude =
    s"""From SSL_Iris Require Import core.
       |From iris.program_logic Require Export weakestpre.
       |From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
       |From iris.heap_lang Require Import lang notation proofmode.
       |From iris_string_ident Require Import ltac2_string_ident.
       |From Hammer Require Import Hammer.
       |Context `{!heapG Σ}.
       |Set Default Proof Using "Type".
       |
       |Axiom NilNotLval:
       |  forall x v,
       |  x ↦ v -∗ x ↦ v ∗ ⌜x ≠ null_loc⌝.
       |
       |""".stripMargin

  def pp : String = {
    val b = new StringBuilder
    b.append(prelude)
    b.append(predicates.map(_.pp).mkString("\n"))
    b.append("\n")
    b.append(predicates.flatMap(_.getHelpers).map(_.pp).mkString("\n"))
    b.append(helperSpecs.map(_.pp).mkString("\n"))
    b.append(funDef.pp)
    b.append("\n")
    b.append(funSpec.pp)
    b.append("Proof.\n")
    b.append(proofStr)
    b.append("Qed.\n")
    b.toString()
  }

  override def outputs: List[CertificateOutput] =  List(CoqOutput(s"$name.v", name, pp))
}
