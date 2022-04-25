package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.{CertTree, CertificateOutput, CertificationTarget}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Proof
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.translation.Translation
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Specifications.Goal

case class VST() extends CertificationTarget {
  type T = VST
  type P = VSTPredicate
  override val name: String = "VST"
  override val suffix: String = ".v"

  val common_coq_lib_name = "common"

  override def certify(testName: String, proc: Procedure, tree: ProofTree[SuslikProofStep], goal: Goal, env: Environment): VSTCertificate = {
    Translation.translate(testName, tree, proc, env)
  }


  def generate_common_definitions_of(base_filename: String, predicates: List[VSTPredicate]): List[CertificateOutput] = {
    List(
      CProcedureDefinition.common_c_header(base_filename),
      CProcedureDefinition.common_c_file(base_filename),
      Proof.common_predicates(base_filename, predicates)
    )
  }
}

