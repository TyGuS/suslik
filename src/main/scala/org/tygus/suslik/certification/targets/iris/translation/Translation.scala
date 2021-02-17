package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.{CertTree, SuslikProofStep}
import org.tygus.suslik.certification.targets.iris.IrisCertificate
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HFunDef
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def translate(node: CertTree.Node, proc: Procedure)(implicit env: Environment): IrisCertificate = {

    val suslikTree = SuslikProofStep.of_certtree(node)
    val progTree = ProgramEvaluator.run(suslikTree)(ProgramTranslator, ProgramContext())
    val funDef = HFunDef(proc.name, proc.formals.map(_.translate), progTree)

    IrisCertificate(proc.name, funDef)
  }
}