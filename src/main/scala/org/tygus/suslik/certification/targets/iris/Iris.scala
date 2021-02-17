package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.targets.iris.translation.Translation
import org.tygus.suslik.certification.{CertTree, CertificationTarget, SuslikProofStep}
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.iris.translation.Translation.TranslationException

object Iris extends CertificationTarget {
  val name: String = "HTT"
  val suffix: String = ".v"

  def certify(proc: Procedure, env: Environment) : IrisCertificate = {
    val root = CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    val cert = Translation.translate(root, proc)(env)

    val simplified = SuslikProofStep.of_certtree(root)
    println(s"Suslik Proof:\n ${SuslikProofStep.ProofTreePrinter.pp(simplified)}")

    CertTree.clear() // [Certify]: Clear tree after certification complete
    cert
  }

}
