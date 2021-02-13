package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.logic.Proof
import org.tygus.suslik.certification.traversal.StackEvaluator

object ProofEvaluator extends StackEvaluator[SuslikProofStep, Proof.Step, ProofContext]
