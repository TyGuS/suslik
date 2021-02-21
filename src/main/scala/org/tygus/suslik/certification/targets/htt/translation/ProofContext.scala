package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.language.Expressions.{CExpr, CSApp, CSFormula, CSubst, CVar}
import org.tygus.suslik.certification.targets.htt.language.Types.HTTType
import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CAssertion, CInductiveClause, CInductivePredicate}
import org.tygus.suslik.certification.targets.htt.translation.ProofContext.{PredicateEnv, AppliedConstructor}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext

import scala.collection.mutable.ListBuffer

case class ProofContext(predicates: PredicateEnv = Map.empty,
                        postEx: Map[CVar, (HTTType, CExpr)] = Map.empty,
                        appAliases: Map[CSApp, CSApp] = Map.empty,
                        unfoldings: Map[CSApp, AppliedConstructor] = Map.empty,
                        callGoal: Option[Proof.Goal] = None,
                        nextCallId: Int = 0,
                        hints: ListBuffer[Hint] = new ListBuffer[Hint])
  extends ClientContext[Proof.Step] {

  /**
    * Get existentials that result from unfolding an app; heap existentials are provided in
    * their maximally unfolded form (i.e., accounts for nested unfolds)
    */
  def unfoldedAppExistentials(app: CSApp): (Seq[CExpr], Seq[CSFormula]) = {
    unfoldings.get(app) match {
      case Some(constructor) =>
        val heapEx = constructor.asn.sigma.apps.map(unfoldedApp)
        (constructor.existentials, heapEx)
      case _ => (Seq.empty, Seq.empty)
    }
  }

  /**
    * Get the latest version of an app, which may change if one of its argument variables is substituted
    */
  def currentAppAlias(app: CSApp): CSApp = appAliases.get(app) match {
    case None => app
    case Some(app1) => if (app == app1) app else currentAppAlias(app1)
  }

  /**
    * Get the maximally unfolded heap equivalent of an app
    */
  def unfoldedApp(app: CSApp): CSFormula = unfoldings.get(app) match {
    case None => CSFormula(app.heapName, Seq(app), Seq.empty)
    case Some(constructor) =>
      val sigma = constructor.asn.sigma
      val (apps, ptss) = sigma.apps.map(unfoldedApp).map(h => (h.apps, h.ptss)).unzip
      CSFormula(app.heapName, apps.flatten, sigma.ptss ++ ptss.flatten)
  }

  /**
    * Update the current context with new substitutions
    */
  def withSubst(m: Map[CVar, CExpr], affectedApps: Map[CSApp, CSApp]): ProofContext = {
    val postEx1 = postEx.mapValues(v => (v._1, v._2.subst(m)))
    val appAliases1 = affectedApps.foldLeft(appAliases) { case (appAliases, (app, alias)) => appAliases + (app -> alias) + (alias -> alias) }
    val unfoldings1 = unfoldings.map { case (app, constructor) => app.subst(m) -> constructor.subst(m) }
    this.copy(postEx = postEx1, appAliases = appAliases1, unfoldings = unfoldings1)
  }

  def appsAffectedBySubst(m: Map[CVar, CExpr]): Map[CSApp, CSApp] =
    appAliases.foldLeft(Map[CSApp, CSApp]()) { case (affectedApps, (app, alias)) =>
      if (app == alias) {
        val app1 = app.subst(m)
        if (app != app1) {
          affectedApps + (app -> app1)
        } else affectedApps
      } else affectedApps
    }
}

object ProofContext {
  type PredicateEnv = Map[String, CInductivePredicate]
  case class AppliedConstructor(idx: Int, existentials: Seq[CExpr], asn: CAssertion) {
    def subst(sub: CSubst): AppliedConstructor =
      this.copy(existentials = existentials.map(_.subst(sub)), asn = asn.subst(sub))
  }
}
