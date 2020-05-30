package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification._
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

import scala.io.Source

object Coq extends CertificationTarget {
  val name: String = "Coq"

  def certify(proc: Procedure, env: Environment): CoqCertificate = {
    val builder = new StringBuilder
//    val headersFile = "htt-tactics.v"
//    val headers = Source.fromFile(headersFile)
//    for (line <- headers.getLines) builder.append(s"$line\n")
//    headers.close()
//    for (label <- (trace.spec.pre.sigma.apps ++ trace.spec.post.sigma.apps).distinct.map(_.pred)) {
//      val predicate = env.predicates(label)
//      builder.append(Translator.runInductivePredicate(predicate.resolveOverloading(env)).pp)
//      builder.append("\n")
//    }
//    builder.append(Translation.translateFunSpec(env).pp)
//    builder.append("\n")
//    builder.append(Translation.runProcedure(proc, trace).ppp)
//    builder.append("\n")
    builder.append(Translation.translateProof(proc)(env).pp)

    CoqCertificate(builder.toString(), proc.name)
  }
}
