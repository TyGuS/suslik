package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.targets.htt.translation.Translation
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object HTT extends CertificationTarget {
  val name: String = "HTT"
  val suffix: String = ".v"

  def certify(proc: Procedure, env: Environment): HTTCertificate = {
    val root = CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
    Translation.translate(root, proc)(env)
  }
}
