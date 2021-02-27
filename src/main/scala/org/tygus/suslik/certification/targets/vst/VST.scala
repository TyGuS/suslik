package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.{CertTree, CertificationTarget}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.translation.Translation

case class VST() extends CertificationTarget {
  type T = VST
  type P = VSTPredicate
  override val name: String = "VST"
  override val suffix: String = ".v"

  override def certify(proc: Statements.Procedure, env: Environment): VSTCertificate = {
    // retrieve the search tree
    val root =
      CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))

    Translation.translate(root, proc, env)
  }

  def mkDefs(predicates: List[VSTPredicate]): String = ???
}

