package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.iris.IrisCertificate
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HFunDef
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.certification.targets.iris.translation.IrisTranslator._

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def translate(node: CertTree.Node, proc: Procedure)(implicit env: Environment): IrisCertificate = {

    val suslikTree = SuslikProofStep.of_certtree(node)
    val params = proc.formals.map(_.translate)

    // We have this "dummy" value to generate progToSpec for the actual context, ctx
    val pre_ctx = Some(TranslationContext(env, node.goal.gamma, Map.empty, node.goal.gamma.translate))
    val progToSpec = params.map(p => (p, p.translate(progVarToSpecQuantifiedValue, pre_ctx)))

    val ctx = TranslationContext(env, node.goal.gamma, progToSpec.toMap, node.goal.gamma.translate)
    val predicates = env.predicates.map({ case (_, pred) => pred.translate(predicateTranslator, Some(ctx))}).toList
    predicates.foreach(p => println(p.pp))

    val progTree = ProgramEvaluator.run(suslikTree, ctx)

    val funDef = HFunDef(proc.name, params, progTree)
    val funSpec = node.goal.translate(goalToFunSpecTranslator, Some(ctx))

    IrisCertificate(proc.name, predicates, funDef, funSpec)
  }
}