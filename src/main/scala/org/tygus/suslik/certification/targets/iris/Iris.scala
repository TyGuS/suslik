package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.source.{SuslikPrinter, SuslikProofStep}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.IPredicate
import org.tygus.suslik.certification.targets.iris.translation.Translation
import org.tygus.suslik.certification.targets.iris.translation.Translation.TranslationException
import org.tygus.suslik.certification.{CertTree, CertificateOutput, CertificationTarget, CoqOutput}
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

case class Iris() extends CertificationTarget {
  type T = Iris
  type P = IPredicate
  val name: String = "HTT"
  val suffix: String = ".v"

  def certify(proc: Procedure, env: Environment): IrisCertificate = {
    val root = CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    val cert = Translation.translate(root, proc)(env)

    val simplified = SuslikProofStep.of_certtree(root)
    println(s"Suslik Proof:\n ${SuslikPrinter.pp(simplified)}")

    cert
  }

  override def generate_common_definitions_of(defFileName: String, predicates: List[IPredicate]): List[CertificateOutput] = {
    def commonPredicates(predicates: List[IPredicate]): String = {
      s"""From SSL_Iris Require Import core.
         |From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
         |From iris.heap_lang Require Import lang notation proofmode.
         |""".stripMargin +
        s"Section common.\n" +
        "Context `{!heapG Σ}.\n" +
      s"${predicates.map(_.pp).mkString("\n")}\n" +
         s"${predicates.flatMap(_.getHelpers).map(_.pp).mkString("\n")}\n" +
      "End common."
    }
    List(CoqOutput(defFileName ++ ".v", defFileName, commonPredicates(predicates)))
  }
}
