package org.tygus.suslik.certification.targets.coq.logic

import org.tygus.suslik.certification.targets.coq.language._
import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.LanguageUtils.cardinalityPrefix
import org.tygus.suslik.logic.Specifications.selfCardVar

sealed abstract class CRuleApp {
  val before: Option[String] = None
  val op: Option[String] = None
  val after: Seq[String] = Seq.empty
  def nextEnvs(env: CEnvironment, goal: CGoal): Seq[CEnvironment] = Seq(env)
  protected def nestedDestruct(items: Seq[CVar]): String = items.toList match {
    case v1 :: v2 :: rest =>
      s"[${v1.pp} ${nestedDestruct(v2 :: rest)}]"
    case v :: _ =>
      v.pp
    case Nil =>
      ""
  }
}


case class CGhostElim(env: CEnvironment) extends CRuleApp {
  override val before: Option[String] = Some("ssl_ghostelim_pre.")
  override val op: Option[String] = {
    val goal = env.goal
    val ghosts = goal.universalGhosts
    if (ghosts.isEmpty) None else {
      val builder = new StringBuilder()
      builder.append("move=>")
      builder.append(nestedDestruct(ghosts))
      builder.append("//=.")
      Some(builder.toString())
    }
  }
  override val after: Seq[String] = {
    val pre = env.goal.pre
    val ptss = pre.sigma.ptss
    val apps = pre.sigma.apps

    val hFromPre = if (apps.nonEmpty) {
      val hApps = nestedDestruct(apps.map(app => CVar(s"H_${app.pred}")))
      if (ptss.nonEmpty) {
        s"[-> $hApps]"
      } else {
        hApps
      }
    } else if (ptss.nonEmpty) {
      "->"
    }
    val builder = new StringBuilder()
    builder.append("move=>")
    builder.append(hFromPre)
    builder.append(" HValid.")
    Seq(builder.toString())
  }

  override def nextEnvs(env: CEnvironment, goal: CGoal): Seq[CEnvironment] = {
    val goal = env.goal
    val gamma = goal.gamma
    val universalGhosts = goal.universalGhosts.map(v => (v, gamma.getOrElse(v, CUnitType))).toMap
    val happs = goal.pre.sigma.apps.map(app => (CVar(s"H_${app.pred}"), app))
    val ctx = (universalGhosts ++ happs) + (CVar("h") -> CHeapType)
    Seq(env.copy(goal, ctx = ctx))
  }
}

sealed abstract class CFailRuleApp extends CRuleApp
case object CNoop extends CFailRuleApp
case object CPostInconsistent extends CFailRuleApp
case object CPostInvalid extends CFailRuleApp
case object CAbduceBranch extends CFailRuleApp
case object CHeapUnreachable extends CFailRuleApp

sealed abstract class CLogicalRuleApp extends CRuleApp
case object CEmp extends CLogicalRuleApp {
  override val op: Option[String] = Some("ssl_emp.")
}
case object CInconsistency extends CLogicalRuleApp
case object CFrame extends CLogicalRuleApp
case object CNilNotLval extends CLogicalRuleApp
case object CStarPartial extends CLogicalRuleApp
case object CSubstLeft extends CLogicalRuleApp
case object CSubstLeftVar extends CLogicalRuleApp

sealed abstract class COperationalRuleApp extends CRuleApp
case class CWrite(to: CVar) extends COperationalRuleApp {
  override val op: Option[String] = Some("ssl_write.")
  override val after: Seq[String] = Seq(s"ssl_write_post ${to.pp}.")
}
case object CRead extends COperationalRuleApp {
  override val op: Option[String] = Some("ssl_read.")
}
case object CAlloc extends COperationalRuleApp
case class CFreeRuleApp(size: Int) extends COperationalRuleApp {
  override val op: Option[String] = Some((1 to size).map(_ => "ssl_dealloc.").mkString("\n"))
}

sealed abstract class CUnfoldingRuleApp extends CRuleApp
case class COpen(env: CEnvironment, selectors: Seq[CExpr], app: CSApp) extends CUnfoldingRuleApp {
  val pred: CInductivePredicate = env.predicates(app.pred)

  override val op: Option[String] = {
    val builder = new StringBuilder()
    builder.append("case: ifP=>cond; ")
    builder.append(s"case H_${pred.name}; ")
    builder.append("rewrite cond//==>_.")
    Some(builder.toString())
  }
  override val after: Seq[String] = {
    selectors.map(selector => {
      val builder = new StringBuilder()
      val clause = pred.clauses.find(c => c.selector == selector).get
      val asn = clause.asn
      val ve = (asn.spatialEx ++ asn.pureEx)
        .filter(e => e.name != selfCardVar.name && !e.name.startsWith(cardinalityPrefix))
        .diff(pred.params.map(_._2)).distinct
      val he = asn.heapEx

      // existentials of the constructor
      if (ve.nonEmpty) {
        builder.append(s"move=>${ve.map(v => s"[${v.pp}]").mkString(" ")}.\n")
      }
      // heaps that belong to the recursive predicate occurrence
      if (he.nonEmpty) {
        builder.append(s"move=>${he.map(v => s"[${v.pp}]").mkString(" ")}.\n")
      }
      // constraint from the pure part
      builder.append(s"move=>[E].\n")
      // substituting the elaborated heap
      builder.append("move=>[->].\n")
      if (asn.sigma.apps.nonEmpty) {
        builder.append(s"move=>")
        builder.append(nestedDestruct(hyps(asn)))
        builder.append(".\n")
      }

      builder.toString()
    })
  }

  private def hyps(asn: CAssertion) : Seq[CVar] = {
    val m: scala.collection.mutable.Map[String, Int] = scala.collection.mutable.Map.empty
    asn.sigma.apps.map(app => m.get(app.pred) match {
      case None =>
        m += (app.pred -> 1)
        CVar(s"H_rec_${app.pred}")
      case Some(count) =>
        m += (app.pred -> (count + 1))
        CVar(s"H_rec_${app.pred}${"'" * count}")
    })
  }

  override def nextEnvs(env: CEnvironment, goal: CGoal): Seq[CEnvironment] = {
    val goal = env.goal
    val gamma = goal.gamma
    selectors.map(selector => {
      val clause = pred.clauses.find(c => c.selector == selector).get
      val asn = clause.asn
      val ve = (asn.spatialEx ++ asn.pureEx).diff(pred.params.map(_._2)).distinct
      val he = asn.heapEx

      val ctx = env.ctx ++ ve.map(v => (v, gamma.getOrElse(v, CUnitType))).toMap[CVar, ProofContextItem]
      val ctx1 = ctx ++ he.map(v => (v, gamma.getOrElse(v, CUnitType))).toMap[CVar, ProofContextItem]
      val ctx2 = ctx1 ++ asn.sigma.apps.map(app => (CVar(s"H_rec_${app.pred}"), app)).toMap[CVar, ProofContextItem]
      env.copy(ctx = ctx2, callHeapVars = he)
    })
  }
}
case class CCallRuleApp(env: CEnvironment, fun: String, args: Seq[CVar], sub: Map[CVar, CExpr]) extends CUnfoldingRuleApp {
  override val before: Option[String] = {
    val builder = new StringBuilder()
    // rearrange heap to put recursive heap component to the head
    builder.append(s"put_to_head ${env.callHeapVars.head.pp}.\n")
    builder.append("apply: bnd_seq.\n")
    // identify how many ghost values to pass to the call
    val pureEx = env.spec.pureParams.map { case (_, v) => sub(v).asInstanceOf[CVar] }
    for (v <- pureEx) builder.append(s"apply: (gh_ex ${v.pp}).\n")
    Some(builder.toString())
  }

  override val op: Option[String] =
    Some(s"apply: val_do=>//= _ ? ->; rewrite unitL=>_.")

  override def nextEnvs(env: CEnvironment, goal: CGoal): Seq[CEnvironment] =
    Seq(env.copy(callHeapVars = env.callHeapVars.tail))
}