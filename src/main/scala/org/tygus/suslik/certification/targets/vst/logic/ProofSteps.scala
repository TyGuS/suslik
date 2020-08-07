package org.tygus.suslik.certification.targets.vst.logic

object ProofSteps {

  sealed abstract class ProofStep {
    def pp: String = ""
  }

}
