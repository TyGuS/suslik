package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HExpr
import org.tygus.suslik.certification.traversal.StackEvaluator

object ProgramEvaluator extends StackEvaluator[SuslikProofStep, HExpr, ProgramContext]
