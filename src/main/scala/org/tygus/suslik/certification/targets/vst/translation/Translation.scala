package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.language.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CFunSpec, CInductivePredicate}
import org.tygus.suslik.certification.targets.vst.logic.Proof.Proof
import org.tygus.suslik.certification.targets.vst.language.Statements.CProcedureDefinition
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)


  def translate(root: CertTree.Node, proc: Procedure, env: Environment):
  (Map[String, CInductivePredicate], CFunSpec, Proof, CProcedureDefinition) = {
    val procedure = CTranslation.translate_function(proc, root.goal.gamma)
    println(procedure.pp)
    print(root.goal.gamma)
    // translate body into VST types, and build context of variables
    // var (body, ctx) = CTranslation.translate_body(proc.f, proc.body, root.goal.gamma)
    // use this to build a C-encoding of the synthesized function
    // var body_string = print_as_c_program(proc.f, body, ctx)
    // print(body_string)


    // translate predicates
    // translate proof
    ???
  }
}
