package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.language.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.logic.ProofSteps.ProofStep

object Proof {

  case class Proof(root: ProofStep, params: Seq[CVar]) {
  }
}
