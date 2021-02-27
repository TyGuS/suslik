package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.source.{SuslikPrinter, SuslikProofStep}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.IPredicate
import org.tygus.suslik.certification.targets.iris.translation.Translation
import org.tygus.suslik.certification.{CertTree, CertificationTarget}
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.iris.translation.Translation.TranslationException

case class Iris() extends CertificationTarget {
  type T = Iris
  type P = IPredicate
  val name: String = "HTT"
  val suffix: String = ".v"

  def certify(proc: Procedure, env: Environment) : IrisCertificate = {
    val root = CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    val cert = Translation.translate(root, proc)(env)

    val simplified = SuslikProofStep.of_certtree(root)
    println(s"Suslik Proof:\n ${SuslikPrinter.pp(simplified)}")

    cert
  }

  override def mkDefs(predicates: List[IPredicate]): String = ???
}
