package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.targets.vst.Types.{CoqIntValType, CoqPtrValType}
import org.tygus.suslik.certification.targets.vst.VSTCertificate
import org.tygus.suslik.certification.targets.vst.logic.{Proof, VSTProofStep}
import org.tygus.suslik.certification.targets.vst.translation.VSTProgramTranslator.VSTProgramContext
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.VSTClientContext
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.certification.traversal.{Evaluator, ProofTree, StackEvaluator, Translator}
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

  def translate_proof[S <: DestStep,C <: Evaluator.ClientContext[S]](proof: ProofTree[SuslikProofStep])(implicit t: Translator[SuslikProofStep, S, C], initial_context:C): ProofTree[S] = {
    val evaluator = new StackEvaluator[SuslikProofStep, S, C] {
      val translator = t
    }
    evaluator.run(proof, initial_context)
  }

  def translate(root: CertTree.Node, proc: Procedure, env: Environment): VSTCertificate = {
    val base_proof = SuslikProofStep.of_certtree(root)
    val predicates = env.predicates.map({ case (_, predicate) => ProofSpecTranslation.translate_predicate(env)(predicate)}).toList
    val params = proc.formals.map({case (Var(name), ty) => ty match {
      case LocType => (name, CoqPtrValType)
      case IntType => (name, CoqIntValType)
    }})
    val (spec, _) = ProofSpecTranslation.translate_conditions(proc.name, params)(root.goal)
    val program_body = translate_proof(base_proof)(new VSTProgramTranslator, VSTProgramTranslator.empty_context)
    val procedure = CProcedureDefinition(proc.name, params, program_body)
    println(procedure.pp)
    println(spec.pp)

    val pred_map = predicates.map(v => (v.name,v)).toMap
    val spec_map = Map(proc.name -> spec)
    val proof_translator = VSTProofTranslator(spec)
    val steps = translate_proof(base_proof)(proof_translator, VSTClientContext.make_context(pred_map, spec_map))

    val proof = Proof(
      proc.f.name, predicates, spec, steps: ProofTree[VSTProofStep],
      uses_free = proof_translator.contains_free,
      uses_malloc = proof_translator.contains_malloc
    )

    VSTCertificate(proc.f.name, procedure, proof)
  }
}
