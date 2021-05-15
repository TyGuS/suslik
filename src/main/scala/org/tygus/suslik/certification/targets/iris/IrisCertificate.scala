package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.targets.iris.IrisCertificate.prelude
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HFunDef
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{IFunSpec, IPredicate}
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget, CoqOutput}

case object IrisCertificate {
  def prelude(importCommon: String = ""): String = {
    s"""From SSL_Iris Require Import core.
       |From iris.program_logic Require Export weakestpre.
       |From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
       |From iris.heap_lang Require Import lang notation proofmode.
       |${importCommon}
       |From iris_string_ident Require Import ltac2_string_ident.
       |From Hammer Require Import Hammer.
       |Context `{!heapG Σ}.
       |Set Default Proof Using "Type".
       |""".stripMargin
  }
}

case class IrisCertificate(testName: String, name: String, predicates: List[IPredicate], funDef: HFunDef, auxSpecs: List[IFunSpec], funSpec: IFunSpec, proofStr: String) extends Certificate[Iris, IPredicate] {
  val target: CertificationTarget = Iris()

  def pp : String = {
    val b = new StringBuilder
    b.append(prelude())
    b.append(predicates.map(_.pp).mkString("\n"))
    b.append("\n")
    b.append(predicates.flatMap(_.getHelpers).map(_.pp).mkString("\n"))
    b.append(auxSpecs.map(_.pp).mkString("\n"))
    b.append(funDef.pp)
    b.append("\n")
    b.append(funSpec.pp)
    b.append("Proof.\n")
    b.append(proofStr)
    b.append("Qed.\n")
    b.toString()
  }

  def ppWithCommonDefs(baseFilename: String, excludedPreds: List[IPredicate]) : String = {
    val exclPredNames = excludedPreds.map(p => p.name)
    val predsToPrint = predicates.filterNot(p => exclPredNames.contains(p.name))

    val b = new StringBuilder
    b.append(prelude(importCommon = s"Require Import $baseFilename."))
    b.append(predsToPrint.map(_.pp).mkString("\n"))
    b.append("\n")
    b.append(predsToPrint.flatMap(_.getHelpers).map(_.pp).mkString("\n"))
    b.append(auxSpecs.map(_.pp).mkString("\n"))
    b.append(funDef.pp)
    b.append("\n")
    b.append(funSpec.pp)
    b.append("Proof.\n")
    b.append(proofStr)
    b.append("Qed.\n")
    b.toString()
  }

  override def outputs: List[CertificateOutput] =  List(CoqOutput(s"$name.v", name, pp))

  override def outputs_with_common_predicates(base_filename: String, common_predicates: List[IPredicate]): List[CertificateOutput] =
    List(CoqOutput(s"$name.v", name, ppWithCommonDefs(base_filename, common_predicates)))

}
