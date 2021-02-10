package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.VSTCertificate
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def fail_with(msg: String) = throw TranslationException(msg)


  def translate(root: CertTree.Node, proc: Procedure, env: Environment): VSTCertificate   = {
    val procedure = CTranslation.translate_function(proc, root.goal.gamma)
    val (spec, context) = ProofSpecTranslation.translate_conditions(procedure)(root.goal)
    val pre_cond = ProofSpecTranslation.translate_assertion(context)(root.goal.pre)
    val post_cond = ProofSpecTranslation.translate_assertion(context)(root.goal.post)
    println(procedure.pp)
    println(spec.pp)
    val predicates: List[VSTPredicate] = env.predicates.map({ case (_, predicate) =>
      ProofSpecTranslation.translate_predicate(env)(predicate)
    }).toList

    predicates.foreach(v => println(v.pp))

    val proof = ProofTranslation.translate_proof(proc.f.name, predicates, spec, root, pre_cond, post_cond)

    println(proof.pp)

    // translate predicates
    // translate proof
    VSTCertificate(proc.f.name, procedure, proof)
  }
}
