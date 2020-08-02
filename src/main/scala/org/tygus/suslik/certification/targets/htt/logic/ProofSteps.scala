package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.Proof._
import org.tygus.suslik.certification.targets.htt.logic.Sentences._

object ProofSteps {
  def nestedDestructR(items: Seq[CExpr]): String = items match {
    case Seq(e1, e2, rest @ _*) =>
      s"[${e1.pp} ${nestedDestructR(e2 +: rest)}]"
    case Seq(e, _*) =>
      e.pp
    case Seq() =>
      ""
  }

  def nestedDestructL(items: Seq[CExpr]): String = {
    def visit(items: Seq[CExpr]): String = items match {
        case Seq(e1, e2, rest @ _*) =>
          s"[${visit(e2 +: rest)} ${e1.pp}]"
        case Seq(e, _*) =>
          e.pp
        case Seq() =>
          ""
      }
    visit(items.reverse)
  }

  sealed abstract class ProofStep {
    def pp: String = ""

    def refreshVars(env: CEnvironment): ProofStep = this

    protected def buildExistentials(builder: StringBuilder, ex: Seq[CExpr], nested: Boolean = false): Unit = {
      if (ex.nonEmpty) {
        if (nested) {
          builder.append(s"move=>${nestedDestructL(ex)}.\n")
        } else {
          builder.append(s"move=>${ex.map(v => s"[${v.pp}]").mkString(" ")}.\n")
        }
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

    protected def existentialInstantiation(builder: StringBuilder, asn: CAssertion, vars: Seq[CExpr], unfoldings: Map[CSApp, CInductiveClause]): Unit = {
      if (vars.nonEmpty) {
        builder.append(s"exists ${vars.map(v => s"(${v.pp})").mkString(", ")};\n")
      }

      def unfoldSAppExistentials(app: CSApp): (Seq[CPointsTo], Seq[CSApp]) = unfoldings.get(app) match {
        case Some(a) =>
          val sigma = a.asn.sigma
          val (ptss, apps) = sigma.apps.map(unfoldSAppExistentials).unzip
          (sigma.ptss ++ ptss.flatten, apps.flatten)
        case None =>
          (Seq.empty, Seq(app))
      }

      val apps = asn.sigma.apps
      for (app <- apps) {
        val (unfoldedPtss, unfoldedApps) = unfoldSAppExistentials(app)
        val h = CSFormula("", unfoldedApps, unfoldedPtss)
        builder.append(s"exists (${h.ppHeap});\n")
      }

      // solve everything except sapps
      builder.append("ssl_emp_post.\n")

      for {
        app <- apps
        c <- unfoldings.get(app)
      } {
        builder.append(s"unfold_constructor ${c.idx + 1};\n")
        existentialInstantiation(builder, c.asn, c.existentials, unfoldings)
      }
    }

    def vars: Set[CVar] = {
      def collector(acc: Set[CVar])(st: ProofStep): Set[CVar] = st match {
        case WriteStep(to, _, e, _) =>
          acc ++ to.vars ++ e.vars
        case ReadStep(to, from) =>
          acc ++ to.vars ++ from.vars
        case AllocStep(to, _, _) =>
          acc ++ to.vars
        case SeqCompStep(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case CallStep(goal, freshToActual, _) =>
          acc ++ goal.existentials ++ freshToActual.values.flatMap(_.vars)
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
        case (ReadStep(to, _), _) => simplifyBinding(to)
//        case (WriteStep(to), _) => simplifyBinding(to)
//        case (AllocStep(to, _, _), _) => simplifyBinding(to)
        case _ => this
      }
    }

    def simplifyBinding(newvar: CVar): ProofStep = {
      val used = s2.vars
      if (used.contains(newvar)) {
        this
      } else s2 // Do not generate bindings for unused variables
    }
  }

  case class WriteStep(to: CVar, offset: Int, e: CExpr, frame: Boolean = true) extends ProofStep {
    override def refreshVars(env: CEnvironment): WriteStep =
      WriteStep(env.ghostSubst.getOrElse(to, to), offset, e.subst(env.ghostSubst), frame)

    override def pp: String = {
      val ptr = if (offset == 0) to.pp else s"(${to.pp} .+ $offset)"
      val writeStep = "ssl_write.\n"
      val writePostStep = if (frame) s"ssl_write_post $ptr.\n" else ""
      writeStep + writePostStep
    }
  }

  case class ReadStep(to: CVar, from: CVar) extends ProofStep {
    override def refreshVars(env: CEnvironment): ReadStep =
      ReadStep(env.ghostSubst.getOrElse(to, to), env.ghostSubst.getOrElse(from, from))

    override def pp: String = "ssl_read.\n"
  }

  case class AllocStep(to: CVar, tpe: HTTType, sz: Int) extends ProofStep {
    override def refreshVars(env: CEnvironment): AllocStep =
      AllocStep(env.ghostSubst.getOrElse(to, to), tpe, sz)

    override def pp: String = s"ssl_alloc ${to.pp}.\n"
  }

  case class FreeStep(size: Int) extends ProofStep {
    override def pp: String = {
      val deallocStmts = (1 to size).map(_ => "ssl_dealloc.")
      s"${deallocStmts.mkString("\n")}\n"
    }
  }

  case object OpenStep extends ProofStep {
    override def pp: String = "ssl_open.\n"
  }

  case class OpenPostStep(app: CSApp, pre: CAssertion, existentials: Seq[CExpr]) extends ProofStep {
    override def refreshVars(env: CEnvironment): OpenPostStep = OpenPostStep(
      app.subst(env.ghostSubst),
      pre.subst(env.ghostSubst),
      existentials.map(v => v.subst(env.ghostSubst))
    )

    override def pp: String = {
      val builder = new StringBuilder()
      builder.append(s"ssl_open_post ${app.hypName}.\n")

      buildExistentials(builder, existentials)
      buildExistentials(builder, pre.heapVars)

      buildHeapExpansion(builder, pre, app.uniqueName)

      builder.toString()
    }
  }

  case class CallStep(goal: CGoal, freshToActual: Map[CVar, CExpr], callId: String) extends ProofStep {
    override def refreshVars(env: CEnvironment): CallStep = CallStep (
      goal.subst(env.ghostSubst),
      freshToActual.mapValues(e => e.subst(env.ghostSubst).subst(env.subst)),
      callId
    )

    override def pp: String = {
      val builder = new StringBuilder()

      val refreshedPre = goal.pre.subst(freshToActual)
      val refreshedPost = goal.post.subst(freshToActual)
      val refreshedGhosts = goal.universalGhosts.map(_.subst(freshToActual))
      val callHeap = refreshedPre.sigma

      // put the part of the heap touched by the recursive call at the head
      builder.append(s"ssl_call_pre (${callHeap.ppHeap}).\n")

      // provide universal ghosts and execute call
      builder.append(s"ssl_call (${refreshedGhosts.map(_.pp).mkString(", ")}).\n")

      // pre has no value existentials
      existentialInstantiation(builder, refreshedPre, Seq.empty, Map.empty)

      builder.append(s"move=>h_$callId.\n")

      buildExistentials(builder, goal.existentials)
      buildExistentials(builder, refreshedPost.heapVars)
      buildHeapExpansion(builder, refreshedPost, callId)

      // store validity hypotheses in context
      builder.append("store_valid.\n")

      builder.toString()
    }
  }

  case class GhostElimStep(goal: CGoal) extends ProofStep {
    override def refreshVars(env: CEnvironment): GhostElimStep =
      GhostElimStep(goal.subst(env.ghostSubst))

    override def pp: String = {
      val builder = new StringBuilder()

      // Pull out any precondition ghosts and move precondition heap to the context
      builder.append("ssl_ghostelim_pre.\n")

      buildExistentials(builder, goal.universalGhosts, nested = true)
      buildExistentials(builder, goal.pre.heapVars)
      buildHeapExpansion(builder, goal.pre, "self")

      // store heap validity assertions
      builder.append("ssl_ghostelim_post.\n")

      builder.toString()
    }
  }

  case object AbduceBranchStep extends ProofStep {
    override def pp: String = "ssl_abduce_branch.\n"
  }

  case class EmpStep(goal: CGoal, sub: Map[CVar, CExpr], unfoldings: Map[CSApp, CInductiveClause]) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()
      builder.append("ssl_emp;\n")

      val post = goal.post.subst(sub)
      val postEx = goal.existentials.map(_.subst(sub))
      val unfoldings1 = unfoldings.map { case (app, e) => app.subst(sub) -> e.subst(sub) }
      existentialInstantiation(builder, post, postEx, unfoldings1)

      builder.toString()
    }
  }
}
