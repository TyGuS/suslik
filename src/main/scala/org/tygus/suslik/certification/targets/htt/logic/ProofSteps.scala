package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language._
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.Proof._

object ProofSteps {
  case class Proof(root: ProofStep) {
    def pp: String = s"Next Obligation.\n${root.pp}\nQed.\n"
  }
  sealed abstract class ProofStep {
    def pp: String = ""

    protected def nestedDestructR(items: Seq[CVar]): String = items.toList match {
      case v1 :: v2 :: rest =>
        s"[${v1.pp} ${nestedDestructR(v2 :: rest)}]"
      case v :: _ =>
        v.pp
      case Nil =>
        ""
    }

    protected def nestedDestructL(items: Seq[CVar]): String = {
      def visit(items: Seq[CVar]): String = {
        items.toList match {
          case v1 :: v2 :: rest =>
            s"[${visit(v2 :: rest)} ${v1.pp}]"
          case v :: _ =>
            v.pp
          case Nil =>
            ""
        }
      }
      visit(items.reverse)
    }

    protected def buildValueExistentials(builder: StringBuilder, asn: CAssertion, outsideVars: Seq[CVar], nested: Boolean = false): Unit = {
      val ve = asn.valueVars.diff(outsideVars)

      // move value existentials to context
      if (ve.nonEmpty) {
        if (nested) {
          builder.append(s"move=>${nestedDestructL(ve)}.\n")
        } else {
          builder.append(s"move=>${ve.map(v => s"[${v.pp}]").mkString(" ")}.\n")
        }
      }
    }

    protected def buildHeapExistentials(builder: StringBuilder, asn: CAssertion, outsideVars: Seq[CVar]): Unit = {
      val he = asn.heapVars.diff(outsideVars)

      // move heap existentials to context
      if (he.nonEmpty) {
        builder.append(s"move=>${he.map(v => s"[${v.pp}]").mkString(" ")}.\n")
      }
    }

    protected def buildHeapExpansion(builder: StringBuilder, asn: CAssertion, uniqueName: String): Unit = {
      val phi = asn.phi
      val sigma = asn.sigma
      val phiName = s"phi_$uniqueName"
      val sigmaName = s"sigma_$uniqueName"

      // move pure part to context
      if (!phi.isTrivial) {
        builder.append(s"move=>[$phiName].\n")
      }

      // move spatial part to context, and then substitute where appropriate
      builder.append(s"move=>[$sigmaName].\n")
      builder.append(s"rewrite->$sigmaName in *.\n")

      // move predicate apps to context, if any
      if (sigma.apps.nonEmpty) {
        val appNames = sigma.apps.map(app => CVar(app.hypName))
        val hApps = nestedDestructR(appNames)
        builder.append(s"move=>$hApps.\n")
      }
    }

    protected def existentialInstantiation(builder: StringBuilder, asn: CAssertion, ve: Seq[CExpr], heapSubst: Map[CSApp, AppExpansion]): Unit = {
      if (ve.nonEmpty) {
        builder.append(s"exists ${ve.map(v => s"(${v.pp})").mkString(", ")}.\n")
      }

      def expandSAppExistentials(app: CSApp): (Seq[CPointsTo], Seq[CSApp]) = heapSubst.get(app) match {
        case Some(e) =>
          val (ptss, apps) = e.heap.apps.map(expandSAppExistentials).unzip
          (e.heap.ptss ++ ptss.flatten, apps.flatten)
        case None =>
          (Seq.empty, Seq(app))
      }

      val apps = asn.sigma.apps
      for (app <- apps) {
        val (expandedPtss, expandedApps) = expandSAppExistentials(app)
        val h = CSFormula("", expandedApps, expandedPtss)
        builder.append(s"exists (${h.ppHeap});\n")
      }

      // solve everything except sapps
      builder.append("ssl_emp_post.\n")

      for {
        app <- apps
        ae@AppExpansion(constructor, heap, _) <- heapSubst.get(app)
      } {
        builder.append(s"unfold_constructor ${constructor + 1};\n")
        existentialInstantiation(builder, CAssertion(CBoolConst(true), heap), ae.ex, heapSubst)
      }
    }

    def vars: Set[CVar] = {
      def collector(acc: Set[CVar])(st: ProofStep): Set[CVar] = st match {
        case WriteStep(to, _, e) =>
          acc ++ to.vars ++ e.vars
        case ReadStep(to) =>
          acc ++ to.vars
        case AllocStep(to, _, _) =>
          acc ++ to.vars
        case SeqCompStep(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case CallStep(pre, post, vars, pureEx) =>
          val c1 = pre.sigma.vars
          val c2 = post.sigma.vars
          val c3 = pureEx.flatMap(e => e.vars).toSet
          acc ++ c1 ++ c2 ++ c3
        case _ =>
          acc
      }

      collector(Set.empty)(this)
    }
  }

  case class SeqCompStep(s1: ProofStep, s2: ProofStep) extends ProofStep {
    override def pp: String = s"${s1.pp}${s2.pp}"

    def simplify: ProofStep = {
      (s1, s2) match {
        case (ReadStep(to), _) => simplifyBinding(to)
//        case (WriteStep(to), _) => simplifyBinding(to)
//        case (AllocStep(to, _, _), _) => simplifyBinding(to)
        case _ => this
      }
    }

    def simplifyBinding(newvar: CVar): ProofStep = {
      val used = s2.vars
      if (used.exists(v => newvar.name.startsWith(v.name))) {
        this
      } else s2 // Do not generate bindings for unused variables
    }
  }

  case class WriteStep(to: CVar, offset: Int, e: CExpr) extends ProofStep {
    override def pp: String = {
      val ptr = if (offset == 0) to.pp else s"(${to.pp} .+ $offset)"
      s"ssl_write.\nssl_write_post $ptr.\n"
    }
  }

  case class ReadStep(to: CVar) extends ProofStep {
    override def pp: String = "ssl_read.\n"
  }

  case class AllocStep(to: CVar, tpe: CoqType, sz: Int) extends ProofStep {
    override def pp: String = s"ssl_alloc ${to.pp}.\n"
  }

  case class FreeStep(size: Int) extends ProofStep {
    override def pp: String = {
      val deallocStmts = (1 to size).map(_ => "ssl_dealloc.")
      s"${deallocStmts.mkString("\n")}\n"
    }
  }

  case object OpenStep extends ProofStep {
    override def pp: String = "case: ifP=>H_cond.\n"
  }

  case class OpenPostStep(app: CSApp, goal: CGoal) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()
      builder.append(s"case ${app.hypName}; rewrite H_cond=>//= _.\n")

      buildValueExistentials(builder, goal.pre, app.vars)
      buildHeapExistentials(builder, goal.pre, app.vars)

      buildHeapExpansion(builder, goal.pre, app.uniqueName)

      builder.toString()
    }
  }

  case class CallStep(pre: CAssertion, post: CAssertion, outsideVars: Seq[CVar], pureEx: Seq[CExpr]) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()

      val callHeap = pre.sigma

      // put the part of the heap touched by the recursive call at the head
      builder.append(s"ssl_call_pre (${callHeap.ppHeap}).\n")

      // provide universal ghosts and execute call
      builder.append(s"ssl_call (${pureEx.map(_.pp).mkString(", ")}).\n")

      existentialInstantiation(builder, pre, pre.valueVars.diff(outsideVars), Map.empty)

      val callId = s"call${scala.math.abs(pre.hashCode())}"
      builder.append(s"move=>h_$callId.\n")

      buildValueExistentials(builder, post,  outsideVars)
      buildHeapExistentials(builder, post,  outsideVars)
      buildHeapExpansion(builder, post, callId)

      // store validity hypotheses in context
      builder.append("store_valid.\n")

      builder.toString()
    }
  }

  case class GhostElimStep(goal: CGoal) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()

      // Pull out any precondition ghosts and move precondition heap to the context
      builder.append("ssl_ghostelim_pre.\n")

      buildValueExistentials(builder, goal.pre, goal.programVars, nested = true)
      buildHeapExistentials(builder, goal.pre, goal.programVars)
      buildHeapExpansion(builder, goal.pre, "root")

      // store heap validity assertions
      builder.append("ssl_ghostelim_post.\n")

      builder.toString()
    }
  }

  case object AbduceBranchStep extends ProofStep {
    override def pp: String = "case: ifP=>H_cond.\n"
  }

  case class EmpStep(cenv: CEnvironment) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()
      builder.append("ssl_emp;\n")

      val ghostSubst = cenv.ghostSubst
      val subst = cenv.subst.mapValues(_.subst(ghostSubst))
      val post = cenv.spec.post.subst(ghostSubst)
      val programVars = cenv.spec.programVars.map(v => ghostSubst.getOrElse(v, v))
      val ve = post.valueVars.diff(programVars).distinct.map(_.subst(subst))
      val heapSubst = cenv.heapSubst.map { case (app, e) =>
        val app1 = app.subst(ghostSubst).subst(subst).asInstanceOf[CSApp]
        val e1 = AppExpansion(
          e.constructor,
          e.heap.subst(ghostSubst).subst(subst).asInstanceOf[CSFormula],
          e.ex.map(_.subst(ghostSubst).subst(subst))
        )
        app1 -> e1
      }
      existentialInstantiation(builder, post.subst(subst), ve, heapSubst)

      builder.toString()
    }
  }
}
