package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.targets.htt.translation.Translation
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object HTT extends CertificationTarget {
  val name: String = "HTT"
  val suffix: String = ".v"
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

  def certify(proc: Procedure, env: Environment): HTTCertificate = {
    val root = CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    Translation.translate(root, proc)(env)
  }

  def mkDefs(predicates: List[Predicate]): String = {
    s"$prelude\n${predicates.map(_.pp).mkString("\n\n")}"
  }
}
