package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.targets.htt.logic.Sentences.CInductivePredicate
import org.tygus.suslik.certification.targets.htt.translation.Translation
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

case class HTT() extends CertificationTarget {
  type T = HTT
  type P = CInductivePredicate
  val name: String = "HTT"
  val suffix: String = ".v"

  def certify(proc: Procedure, env: Environment): HTTCertificate = {
    val root = CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    Translation.translate(root, proc)(env)
  }

  def generate_common_definitions_of(defFileName: String, predicates: List[CInductivePredicate]): List[CertificateOutput] = {
    List(CoqOutput(defFileName ++ ".v", defFileName, s"${HTT.prelude}\n${predicates.map(_.pp).mkString("\n\n")}"))
  }
}

object HTT {
  val prelude =
    """From mathcomp
      |Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
      |From fcsl
      |Require Import prelude pred pcm unionmap heap.
      |From HTT
      |Require Import stmod stsep stlog stlogR.
      |From SSL
      |Require Import core.
      |
      |""".stripMargin

}