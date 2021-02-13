package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.program.Statements.CStatement
import org.tygus.suslik.certification.traversal.StackEvaluator

object ProgramEvaluator extends StackEvaluator[SuslikProofStep, CStatement, ProgramContext]
