package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.targets.coq.Translation.TranslationException
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

import scala.io.Source

object Coq extends CertificationTarget {
  val name: String = "Coq"
  lazy val root: Tree.Node = Tree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))

  def certify(proc: Procedure, env: Environment): CoqCertificate = {
    val builder = new StringBuilder
    val headersFile = "htt-tactics.v"
    val headers = Source.fromFile(headersFile)
    for (line <- headers.getLines) builder.append(s"$line\n")
    headers.close()
    for (label <- (root.goal.pre.sigma.apps ++ root.goal.post.sigma.apps).distinct.map(_.pred)) {
      val predicate = env.predicates(label)
      builder.append(Translation.translateInductivePredicate(predicate.resolveOverloading(env)).pp)
      builder.append("\n")
    }
    val (spec, proof, cproc) = Translation.translate(root, proc)(env)
    builder.append(spec.pp)
    builder.append("\n")
    builder.append(cproc.ppp)
    builder.append("\n")
    builder.append(proof.pp)

    CoqCertificate(builder.toString(), proc.name)
  }
}
