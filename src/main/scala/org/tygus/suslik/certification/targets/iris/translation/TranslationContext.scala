package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HExpr, HProgVar}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.IQuantifiedVar
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.logic.Gamma

case class TranslationContext(gamma: Gamma, pts: Map[HProgVar, IQuantifiedVar]) extends ClientContext[HExpr]