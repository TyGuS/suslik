package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.targets.coq.Translation.TranslationException
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

import scala.io.Source

object Coq extends CertificationTarget {
  val name: String = "Coq"

  def certify(proc: Procedure, env: Environment): CoqCertificate = {
    val root = Tree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    val builder = new StringBuilder
    val headersFile = "htt-tactics.v"
    val headers = Source.fromFile(headersFile)
    for (line <- headers.getLines) builder.append(s"$line\n")
    headers.close()
    val (preds, spec, proof, cproc) = Translation.translate(root, proc)(env)
    preds.foreach(pred => builder.append(pred.pp + "\n"))
    builder.append(spec.pp)
    builder.append("\n")
    builder.append(cproc.ppp)
    builder.append("\n")
    builder.append(proof.pp)

    Tree.clear() // Clear tree after certification complete

    CoqCertificate(builder.toString(), proc.name)
  }
}
