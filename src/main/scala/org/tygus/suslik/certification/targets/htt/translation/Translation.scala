package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.HTTCertificate
import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences._
import org.tygus.suslik.certification.targets.htt.program.Program
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.logic.{Environment, FunSpec, Gamma, InductivePredicate, Specifications}

import scala.collection.mutable.ListBuffer

object Translation {
  case class TranslationException(msg: String) extends Exception(msg)

  /**
    * Produces the components of a HTT certificate, from the tree of successful derivations and a synthesized procedure
    * @param suslikTree the root of the derivation tree
    * @param proc the synthesized procedure
    * @param env the synthesis environment
    * @return the inductive predicates, fun spec, proof, and program translated to HTT
    */
  def translate(testName: String, suslikTree: ProofTree[SuslikProofStep], goal: Goal, proc: Procedure)(implicit env: Environment): HTTCertificate = {
    val cpreds = env.predicates.mapValues(p => {
      val gamma = p.resolve(p.params.toMap, env).get
      val p1 = p.copy(clauses = p.clauses.map(_.resolveOverloading(gamma)))
      translateInductivePredicate(p1, gamma)
    })

    val auxSpecs = env.functions.values.toSeq.map { spec0 =>
      val FunSpec(name, _, params, pre, post, var_decl) = spec0.resolveOverloading(env)
      val goal = Specifications.topLevelGoal(pre, post, params, name, env, Hole, var_decl)
      goal.translate.toFunspec
    }

    val spec = goal.translate.toFunspec

    val ctx: ProofContext = ProofContext(predicates = cpreds, hints = ListBuffer.empty[Hint], env = env)
    val proofBody = ProofEvaluator.run(suslikTree, ctx)
    val proof = Proof(proofBody)
    val hints = ctx.hints.filter(_.numHypotheses > 0)
    val progBody = ProgramEvaluator.run(suslikTree, ProgramContext(env))
    val cproc = Program(proc.name, proc.tp.translate, proc.formals.map(_.translate), progBody)

    HTTCertificate(testName, cproc.name, cpreds.values.toList, spec, auxSpecs, proof, cproc, hints)
  }

  private def translateInductivePredicate(el: InductivePredicate, gamma: Gamma)(implicit env: Environment): CInductivePredicate = {
    val cParams = el.params.map(_.translate) :+ (CVar("h"), CHeapType)
    val cGamma = gamma.translate

    val cClauses = el.clauses.zipWithIndex.map { case (c, idx) =>
      val selector = c.selector.translate
      val asn = c.asn.translate

      // Include the clause number so that we can use Coq's `constructor n` tactic
      CInductiveClause(el.name, idx + 1, selector, asn, asn.existentials(cParams.map(_._1)))
    }
    CInductivePredicate(el.name, cParams, cClauses, cGamma)
  }
}
