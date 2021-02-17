package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.targets.vst.Types.{CoqIntValType, CoqPtrValType}
import org.tygus.suslik.certification.targets.vst.VSTCertificate
import org.tygus.suslik.certification.targets.vst.logic.{Proof, VSTProofStep}
import org.tygus.suslik.certification.targets.vst.translation.VSTProgramTranslator.VSTProgramContext
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.VSTClientContext
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.certification.traversal.{Evaluator, ProofTree, StackEvaluator, Translator}
import org.tygus.suslik.certification.{CertTree, SuslikProofStep}
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.{IntType, LocType}
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def fail_with(msg: String) = throw TranslationException(msg)

  def translate_proof[S <: DestStep,C <: Evaluator.ClientContext[S]](proof: ProofTree[SuslikProofStep])(translator: Translator[SuslikProofStep, S, C], initial_context:C): ProofTree[S] = {
    val evaluator = new StackEvaluator[SuslikProofStep, S, C]
    evaluator.run(proof)(translator, initial_context)
  }

  def translate(root: CertTree.Node, proc: Procedure, env: Environment): VSTCertificate = {
    val base_proof = SuslikProofStep.of_certtree(root)

    //    val procedure: Statements.CProcedureDefinition = CTranslation.translate_function(proc, root.goal.gamma)
    //    val new_procedure : Statements.CProcedureDefinition = CTranslation.translate_function_from_proof(base_proof, root.goal.gamma)

    //    val (spec, context) = ProofSpecTranslation.translate_conditions(procedure)(root.goal)
    //    val pre_cond = ProofSpecTranslation.translate_assertion(context)(root.goal.pre)
    //    val post_cond = ProofSpecTranslation.translate_assertion(context)(root.goal.post)

    //    println(procedure.pp)
    //    println(new_procedure.pp)
    val predicates = env.predicates.map({ case (_, predicate) => ProofSpecTranslation.translate_predicate(env)(predicate)}).toList
    predicates.foreach(v => println(v.pp))
    val params = proc.formals.map({case (Var(name), ty) => ty match {
      case LocType => (name, CoqPtrValType)
      case IntType => (name, CoqIntValType)
    }})
    val (spec, _) = ProofSpecTranslation.translate_conditions(proc.name, params)(root.goal)
    println(spec.pp)
    val program_steps = translate_proof(base_proof)(new VSTProgramTranslator, VSTProgramContext(Map()))
    val procedure = ???



    val pred_map = predicates.map(v => (v.name,v)).toMap
    val steps = translate_proof(base_proof)(new VSTProofTranslator, VSTClientContext.make_context(pred_map))

    val proof = Proof(proc.f.name, predicates, spec, steps: ProofTree[VSTProofStep])

    VSTCertificate(proc.f.name, procedure, proof)
  }
}
