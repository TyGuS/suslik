package org.tygus.suslik.certification.targets.coq.logic.rules

import org.tygus.suslik.certification.targets.coq.language._
import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.logic.Proof._
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp

object UnfoldingRules {
  case class COpenApp(selectors: Seq[CExpr], pred: CInductivePredicate, env: CEnvironment) extends CRuleApp(env) {
    private val clauses: Seq[CInductiveClause] = selectors.map(s => pred.clauses.find(_.selector == s).get)

    // maps from apps to coq proof names
    private val clauseAppNames: Seq[Seq[CVar]] = clauses.map {
      _.asn.sigma.apps.map(app => env.generateFreshVar(CVar(s"H_${app.pred}")))
    }

    // run this to generate my descendants each with an updated context
    override val nextEnvs: Seq[CEnvironment] = {
      clauses.zip(clauseAppNames).map { case (clause, appNames) =>
        val asn = clause.asn
        val ve = (asn.spatialEx ++ asn.pureEx).diff(pred.params.map(_._2)).distinct
        val he = asn.heapEx
        env.copy(ctx = env.ctx ++ ve ++ he ++ appNames, callHeapVars = he)
      }
    }

    // run this after all my descendants return
    override def fn(steps: Seq[String]): String = {
      val builder = new StringBuilder()
      builder.append("case: ifP=>H_cond.\n")
      clauses.zip(steps).zip(clauseAppNames).foreach { case ((clause, step), appNames) =>
        // match current condition to correct constructor
        builder.append(s"case H_${pred.name}; rewrite H_cond=>//= _.\n")

        val asn = clause.asn
        val ve = (asn.spatialEx ++ asn.pureEx).diff(pred.params.map(_._2)).distinct
        val he = asn.heapEx
        val ptss = asn.sigma.ptss
        val apps = asn.sigma.apps

        // move constructor's value existentials to context
        if (ve.nonEmpty) {
          builder.append(s"move=>${ve.map(v => s"[${v.pp}]").mkString(" ")}.\n")
        }

        // move constructor's heap existentials to context
        if (he.nonEmpty) {
          builder.append(s"move=>${he.map(v => s"[${v.pp}]").mkString(" ")}.\n")
        }

        // move constructor's pure part to context
        builder.append(s"move=>[${pred.name}_phi].\n")

        // substitute constructor's points-to assertions to conclusion
        if (ptss.nonEmpty || apps.isEmpty) {
          builder.append("move=>[->].\n")
        }

        // move constructor's predicate apps to context
        if (appNames.nonEmpty) {
          val hApps = nestedDestruct(appNames)
          builder.append(s"move=>$hApps.\n")
        }

        builder.append(step)

      }

      builder.append("\n")
      builder.toString()
    }
  }

  case class CCallApp(fun: String, sub: Map[CVar, CExpr], env: CEnvironment) extends CRuleApp(env) {
    override val nextEnvs: Seq[CEnvironment] =
      Seq(env.copy(callHeapVars = env.callHeapVars.tail))

    override def fn(steps: Seq[String]): String = {
      val builder = new StringBuilder()
      // rearrange heap to put recursive heap component to the head
      builder.append(s"put_to_head ${env.callHeapVars.head.pp}.\n")
      builder.append("apply: bnd_seq.\n")
      // identify how many ghost values to pass to the call
      val pureEx = env.spec.pureParams.map { case (_, v) => sub(v).asInstanceOf[CVar] }
      for (v <- pureEx) builder.append(s"apply: (gh_ex ${v.pp}).\n")

      builder.append("apply: val_do=>//= _ ? ->; rewrite unitL=>_.\n")

      // print the rest
      steps.headOption.foreach(builder.append)

      builder.toString()
    }
  }
}
