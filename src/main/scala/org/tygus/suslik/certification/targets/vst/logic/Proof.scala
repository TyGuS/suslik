package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.language.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.logic.ProofSteps.ProofStep
import org.tygus.suslik.language.Ident

object Proof {


  case class VSTClause() {

  }
  case class VSTPredicate(
                           predicate_name: Ident,
                           params: Seq[(CVar, org.tygus.suslik.certification.targets.vst.language.Types.VSTType)],

                         ) {

  }

  case class Proof(root: ProofStep, params: Seq[CVar]) {
  }

}
