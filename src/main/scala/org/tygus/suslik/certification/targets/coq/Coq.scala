package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.targets.coq.translation.Translation
import org.tygus.suslik.certification.targets.coq.translation.Translation.TranslationException
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object Coq extends CertificationTarget {
  val name: String = "Coq"
  private val prelude = """
From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

"""

  def certify(proc: Procedure, env: Environment): CoqCertificate = {
    val root = CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    val builder = new StringBuilder
    builder.append(prelude)
    val (preds, spec, proof, cproc) = Translation.translate(root, proc)(env)
    preds.foreach(pred => builder.append(pred.pp + "\n"))
    builder.append(spec.pp)
    builder.append("\n")
    builder.append(cproc.ppp)
    builder.append("\n")
    builder.append(proof.pp)

    CertTree.clear() // [Certify]: Clear tree after certification complete

    CoqCertificate(builder.toString(), proc.name)
  }
}
