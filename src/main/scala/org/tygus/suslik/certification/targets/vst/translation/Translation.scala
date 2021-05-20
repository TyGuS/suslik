package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.targets.vst.Types.{CoqIntValType, CoqPtrValType}
import org.tygus.suslik.certification.targets.vst.VSTCertificate
import org.tygus.suslik.certification.targets.vst.logic.{Proof, VSTProofStep}
import org.tygus.suslik.certification.targets.vst.translation.VSTProgramInterpreter.VSTProgramContext
import org.tygus.suslik.certification.targets.vst.translation.VSTProofInterpreter.VSTClientContext
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.certification.traversal.{Evaluator, ProofTree, StackEvaluator, Interpreter}
import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.{IntType, LocType}
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def fail_with(msg: String) = throw TranslationException(msg)

  def translate_proof[S <: DestStep,C <: Evaluator.ClientContext[S]](proof: ProofTree[SuslikProofStep])(implicit t: Interpreter[SuslikProofStep, S, C], initial_context:C): ProofTree[S] = {
    val evaluator = new StackEvaluator[SuslikProofStep, S, C] {
      val interpreter = t
    }
    evaluator.run(proof, initial_context)
  }

  def translate(testName: String, base_proof: ProofTree[SuslikProofStep], proc: Procedure, env: Environment): VSTCertificate = {
    val predicates = env.predicates.map({ case (_, predicate) => ProofSpecTranslation.translate_predicate(env)(predicate)}).toList
    val pred_map = predicates.map(v => (v.name,v)).toMap
    val pred_type_map = predicates.map(v => (v.name, v.params.map(_._2))).toMap
    var f_gamma = proc.f.gamma(env)
    env.functions.foreach {
      case (_, spec) =>
      val gamma = spec.gamma(env)
    }
    val params = proc.formals.map({case (Var(name), ty) => ty match {
      case LocType => (name, CoqPtrValType)
      case IntType => (name, CoqIntValType)
    }})
    val spec = ProofSpecTranslation.translate_conditions(env)(pred_type_map)(proc.f)
    val helper_specs = env.functions.map {case (fname, spec) => (fname, ProofSpecTranslation.translate_conditions(env)(pred_type_map)(spec))}
    val program_body = translate_proof(base_proof)(new VSTProgramInterpreter, VSTProgramInterpreter.empty_context)
    val procedure = CProcedureDefinition(proc.name, params, program_body, helper_specs.values.toList)

    val spec_map = Map(proc.name -> spec) ++ helper_specs
    val proof_translator = VSTProofInterpreter(spec)
    val steps = translate_proof(base_proof)(proof_translator, VSTClientContext.make_context(pred_map, spec_map))

    val proof = Proof(
      proc.f.name, predicates, spec, steps: ProofTree[VSTProofStep],
      helper_specs,
      uses_free = proof_translator.contains_free,
      uses_malloc = proof_translator.contains_malloc
    )

    VSTCertificate(testName, proc.f.name, procedure, proof)
  }
}
