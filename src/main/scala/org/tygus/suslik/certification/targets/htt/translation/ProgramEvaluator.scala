package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.program.Statements.CStatement
import org.tygus.suslik.certification.traversal.StackEvaluator

object ProgramEvaluator extends StackEvaluator[SuslikProofStep, CStatement, ProgramContext] {
  val interpreter = ProgramInterpreter
}
