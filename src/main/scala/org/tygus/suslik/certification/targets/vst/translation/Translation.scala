package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.VSTCertificate
import org.tygus.suslik.certification.targets.vst.translation.ProofTranslation
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.synthesis.IdProducer.ruleAssert
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}

import scala.annotation.tailrec
import scala.collection.immutable

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def fail_with(msg: String) = throw TranslationException(msg)


  def translate(root: CertTree.Node, proc: Procedure, env: Environment): VSTCertificate   = {
    val procedure = CTranslation.translate_function(proc, root.goal.gamma)
    val (spec, context) = ProofSpecTranslation.translate_conditions(procedure)(root.goal)
    val pre_cond = ProofSpecTranslation.translate_assertion(context)(root.goal.pre)
    println(procedure.pp)
    println(spec.pp)
    val predicates: List[VSTPredicate] = env.predicates.map({ case (_, predicate) =>
      ProofSpecTranslation.translate_predicate(env)(predicate)
    }).toList

    predicates.foreach(v => println(v.pp))

    val proof = ProofTranslation.translate_proof(proc.f.name, predicates, spec, root, pre_cond)

    println(proof.pp)

    // translate predicates
    // translate proof
    VSTCertificate(proc.f.name, procedure, proof)
  }
}
