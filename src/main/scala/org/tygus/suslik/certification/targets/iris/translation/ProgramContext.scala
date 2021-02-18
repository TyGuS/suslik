package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HExpr
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext

case class ProgramContext() extends ClientContext[HExpr]