package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HExpr, HProgVar}
import org.tygus.suslik.certification.targets.iris.heaplang.Types.HType
import org.tygus.suslik.certification.targets.iris.logic.Assertions.IQuantifiedVar
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.language.Ident
import org.tygus.suslik.logic.{Environment, Gamma}

/***
  *
  * @param env
  * @param gamma
  * @param pts mapping between program and quantified spec variables
  * @param hctx heaplang type context used for predicates
  */

case class TranslationContext(env: Environment, gamma: Gamma, pts: Map[HProgVar, IQuantifiedVar], hctx: Map[Ident, HType]) extends ClientContext[HExpr]