package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.source.{SuslikPrinter, SuslikProofStep}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.IPredicate
import org.tygus.suslik.certification.targets.iris.translation.Translation
import org.tygus.suslik.certification.targets.iris.translation.Translation.TranslationException
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.certification.{CertTree, CertificateOutput, CertificationTarget, CoqOutput}
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.logic.Specifications.Goal

case class Iris() extends CertificationTarget {
  type T = Iris
  type P = IPredicate
  val name: String = "Iris"
  val suffix: String = ".v"

  def certify(testName: String, proc: Procedure, tree: ProofTree[SuslikProofStep], goal: Goal, env: Environment): IrisCertificate = {
    val cert = Translation.translate(testName, tree, goal, proc)(env)

    cert
  }

  override def generate_common_definitions_of(defFileName: String, predicates: List[IPredicate]): List[CertificateOutput] = {
    def commonPredicates(predicates: List[IPredicate]): String = {
      s"""From SSL_Iris Require Import core.
         |From iris.heap_lang Require Import lang notation proofmode.
         |From iris_string_ident Require Import ltac2_string_ident.
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
