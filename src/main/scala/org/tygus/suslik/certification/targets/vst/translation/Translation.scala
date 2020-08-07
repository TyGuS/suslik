package org.tygus.suslik.certification.targets.vst.translation



import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.vst.logic.Sentences.CInductivePredicate
import org.tygus.suslik.certification.targets.vst.logic.Sentences.CFunSpec
import org.tygus.suslik.certification.targets.vst.logic.Proof.Proof
import org.tygus.suslik.certification.targets.vst.program.Statements.CProcedure

object Translation {

  def translate(root:CertTree.Node, proc: Procedure, env: Environment) :
    (Map[String, CInductivePredicate], CFunSpec, Proof, CProcedure) = {
    ???
  }
}
