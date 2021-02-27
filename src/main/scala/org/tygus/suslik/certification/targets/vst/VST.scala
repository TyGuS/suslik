package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.{CertTree, Certificate, CertificationTarget, Predicate}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.certification.targets.vst.translation.Translation

object VST extends CertificationTarget {
  override val name: String = "VST"
  override val suffix: String = ".v"

  override def certify(proc: Statements.Procedure, env: Environment): Certificate = {
    // retrieve the search tree
    val root =
      CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))

    Translation.translate(root, proc, env)
  }

  def mkDefs(predicates: List[Predicate]): String = ???
}

