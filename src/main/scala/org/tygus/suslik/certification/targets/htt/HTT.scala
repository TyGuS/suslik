package org.tygus.suslik.certification.targets.htt

import java.nio.file.Paths

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.targets.htt.translation.Translation
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object HTT extends CertificationTarget {
  val name: String = "HTT"
  private val loadPath = Paths.get("certification/htt").toFile.getCanonicalPath
  private val prelude = s"""Add LoadPath "$loadPath" as SSL.
From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

"""

  def certify(proc: Procedure, env: Environment): HTTCertificate = {
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

    HTTCertificate(builder.toString(), proc.name)
  }
}
