package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.language.Expressions.{CExpr, CSApp, CSFormula, CVar}
import org.tygus.suslik.certification.targets.htt.logic.Proof
import org.tygus.suslik.certification.targets.htt.logic.Sentences.CInductiveClause
import org.tygus.suslik.certification.targets.htt.translation.IR.PredicateEnv
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext

case class Context(predicates: PredicateEnv = Map.empty,
                   postEx: Seq[CExpr] = Seq.empty,
                   appAliases: Map[CSApp, CSApp] = Map.empty,
                   unfoldings: Map[CSApp, CInductiveClause] = Map.empty)
  extends ClientContext[Proof.Step] {

  /**
    * Get existentials that result from unfolding an app; heap existentials are provided in
    * their maximally unfolded form (i.e., accounts for nested unfolds)
    */
  def unfoldedAppExistentials(app: CSApp): (Seq[CExpr], Seq[CSFormula]) = {
    unfoldings.get(app) match {
      case Some(clause) =>
        val heapEx = clause.asn.sigma.apps.map(unfoldedApp)
        (clause.existentials, heapEx)
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
    case Some(clause) =>
      val sigma = clause.asn.sigma
      val (apps, ptss) = sigma.apps.map(unfoldedApp).map(h => (h.apps, h.ptss)).unzip
      CSFormula(app.heapName, apps.flatten, sigma.ptss ++ ptss.flatten)
  }

  /**
    * Update the current context with new substitutions
    */
  def withSubst(m: Map[CVar, CExpr]): Context = {
    val postEx1 = postEx.map(_.subst(m))
    val appAliases1 = appAliases.foldLeft(appAliases) { case (appAliases, (app, alias)) =>
      if (app == alias) {
        val app1 = app.subst(m)
        if (app != app1) {
          appAliases + (app -> app1) + (app1 -> app1)
        } else appAliases
      } else appAliases
    }
    val unfoldings1 = unfoldings.map { case (app, clause) => app.subst(m) -> clause.subst(m) }
    this.copy(postEx = postEx1, appAliases = appAliases1, unfoldings = unfoldings1)
  }

  /**
    * Update the current context with a new variable rename
    */
  def withRename(from: CVar, to: CVar): Context = {
    val m = Map(from -> to)
    withSubst(m)
  }
}

object Context {
  val empty: Context = Context()
}
