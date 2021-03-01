package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.source.{SuslikPrinter, SuslikProofStep}
import org.tygus.suslik.certification.targets.iris.IrisCertificate
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HExpr, HFunDef}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.IFunSpec
import org.tygus.suslik.certification.targets.iris.logic.IProofStep
import org.tygus.suslik.certification.targets.iris.logic.IProofStep.ProofTreePrinter
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.iris.translation.IrisTranslator._
import org.tygus.suslik.certification.traversal.{StackEvaluator, Translator}

object ProgramEvaluator extends StackEvaluator[SuslikProofStep, HExpr, ProgramTranslationContext] {
  val translator: Translator[SuslikProofStep, HExpr, ProgramTranslationContext] = ProgramTranslator
}

case class ProofEvaluator(spec: IFunSpec) extends StackEvaluator[SuslikProofStep, IProofStep, IProofContext] {
  val translator: Translator[SuslikProofStep, IProofStep, IProofContext] = ProofTranslator(spec)
}

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def translate(node: CertTree.Node, proc: Procedure)(implicit env: Environment): IrisCertificate = {

    val suslikTree = SuslikProofStep.of_certtree(node)
    val params = proc.formals.map(_.translate)
    println(SuslikPrinter.pp(suslikTree))

    // We have this "dummy" value to generate progToSpec for the actual context, ctx
    val pre_ctx = Some(ProgramTranslationContext(env, node.goal.gamma, Map.empty, node.goal.gamma.translate))
    val progToSpec = params.map(p => (p, p.translate(progVarToSpecVar, pre_ctx)))

    val ctx = ProgramTranslationContext(env, node.goal.gamma, progToSpec.toMap, node.goal.gamma.translate)
    val predicates = env.predicates.map({ case (_, pred) => pred.translate(predicateTranslator, Some(ctx))}).toList
    predicates.foreach(p => println(p.pp))

    val progTree = ProgramEvaluator.run(suslikTree, ctx)

    val funDef = HFunDef(proc.name, params, progTree)
    val funSpec = node.goal.translate(goalToFunSpecTranslator, Some(ctx))


    val predMap = predicates.map(p => (p.name, p)).toMap
    // TODO: add support for helper functions
    val specMap = List((funSpec.fname, funSpec)).toMap

    val proofCtx = IProofContext(0, ctx, predMap, specMap, Map.empty, Map.empty, Map.empty, None)
    val proofStr =
//      try {
        ProofTreePrinter.pp(ProofEvaluator(funSpec).run(suslikTree, proofCtx))
//      }
//      catch { case e =>
//        throw e
//        s"(* Error in proof generation:$e\n${e.getStackTrace.mkString("\n")} *)\n" }

    IrisCertificate(proc.name, predicates, funDef, funSpec, proofStr)
  }
}