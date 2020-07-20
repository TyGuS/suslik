package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language._
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.Proof.CGoal

object ProofSteps {
  case class Proof(root: ProofStep) {
    def pp: String = s"Next Obligation.\n${root.pp}\nQed.\n"
  }
  sealed abstract class ProofStep {
    def pp: String = ""

    protected def nestedDestruct(items: Seq[CVar]): String = items.toList match {
      case v1 :: v2 :: rest =>
        s"[${v1.pp} ${nestedDestruct(v2 :: rest)}]"
      case v :: _ =>
        v.pp
      case Nil =>
        ""
    }

    def collect[R <: CExpr](p: CExpr => Boolean): Set[R] = {
      def collector(acc: Set[R])(st: ProofStep): Set[R] = st match {
        case WriteStep(to, _, e) =>
          acc ++ to.collect(p) ++ e.collect(p)
        case ReadStep(to) =>
          acc ++ to.collect(p)
        case AllocStep(to, _, _) =>
          acc ++ to.collect(p)
        case SeqCompStep(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case CallStep(app, pureEx) =>
          val argVars = app.args.flatMap(arg => arg.collect(p)).toSet
          val pureExVars = pureEx.flatMap(e => e.collect(p)).toSet
          acc ++ argVars ++ pureExVars
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
      val used: Set[CVar] = s2.collect(_.isInstanceOf[CVar])
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

      val asn = goal.pre
      val ve = asn.valueEx.filterNot(app.vars.contains).distinct
      val ptss = goal.pre.sigma.ptss
      val apps = goal.pre.sigma.apps

      // move constructor's value existentials to context
      if (ve.nonEmpty) {
        builder.append(s"move=>${ve.map(v => s"[${v.pp}]").mkString(" ")}.\n")
      }

      // move constructor's heap existentials to context
      if (apps.nonEmpty) {
        builder.append(s"move=>${apps.map(app => s"[${app.heapName}]").mkString(" ")}.\n")
      }

      // move constructor's pure part to context
      builder.append(s"move=>[phi_${app.uniqueName}].\n")

      // substitute constructor's points-to assertions to conclusion
      if (ptss.nonEmpty || apps.isEmpty) {
        builder.append("move=>[->].\n")
      }

      // move constructor's predicate apps to context
      if (apps.nonEmpty) {
        val appNames = apps.map(app => CVar(s"${app.hypName}"))
        val hApps = nestedDestruct(appNames)
        builder.append(s"move=>$hApps.\n")
      }

      builder.toString()
    }
  }

  case class CallStep(app: CSApp, pureEx: Seq[CExpr]) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()

      // rearrange heap to put recursive heap component to the head
      builder.append(s"put_to_head ${app.heapName}.\n")
      builder.append("apply: bnd_seq.\n")

      // identify how many ghost values to pass to the call
      for (v <- pureEx) builder.append(s"apply: (gh_ex ${v.pp}).\n")

      builder.append("apply: val_do=>//= _ ? ->; rewrite unitL=>_.\n")

      builder.toString()
    }
  }

  case class GhostElimStep(goal: CGoal) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()

      // Pull out any precondition ghosts and move precondition heap to the context
      builder.append("ssl_ghostelim_pre.\n")

      val ghosts = goal.universalGhosts
      val pre = goal.pre
      val ptss = pre.sigma.ptss
      val apps = pre.sigma.apps

      // move precondition's ghosts to context
      if (ghosts.nonEmpty) {
        builder.append("move=>")
        builder.append(nestedDestruct(ghosts))
        builder.append("//=.\n")
      }

      // substitute precondition's points-to assertions to conclusion
      if (ptss.nonEmpty || apps.isEmpty) {
        builder.append("move=>[->].\n")
      }

      // move precondition's predicate apps to context
      if (apps.nonEmpty) {
        val hApps = nestedDestruct(apps.map(app => CVar(app.hypName)))
        builder.append(s"move=>$hApps.\n")
      }

      // move heap validity assertion generated by ghR to context
      if (ghosts.nonEmpty) {
        builder.append("ssl_ghostelim_post.\n")
      }

      builder.toString()
    }
  }

  case object AbduceBranchStep extends ProofStep {
    override def pp: String = "case: ifP=>H_cond.\n"
  }

  case class EmpStep(predicates: Seq[CInductivePredicate], spec: CFunSpec, subst: Map[CVar, CExpr], heapSubst: Map[CSApp, (CSFormula, CInductiveClause)]) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()
      builder.append("ssl_emp;\n")


      // instantiate any existentials from the fun spec post
      val post = spec.post
      val postApps = post.sigma.apps
      val programVars = spec.programVars
      val ve = post.valueEx.filterNot(programVars.contains).distinct

      if (ve.nonEmpty) {
        val subs = ve.map(e => e.subst(subst))
        builder.append(s"exists ${subs.map(s => s"(${s.pp})").mkString(", ")};\n")
      }

      // Update heapSubst with the variable substitutions
      val heapSubst1 = heapSubst.map(el => (el._1.subst(subst).asInstanceOf[CSApp], el._2))

      def expand(app: CSApp): Seq[CPointsTo] = {
        val app1 = app.subst(subst).asInstanceOf[CSApp]
        val expandedApp = heapSubst1(app1)._1
        val rest = expandedApp.apps.flatMap(expand)
        expandedApp.ptss ++ rest
      }
      for (postApp <- postApps) {
        val expandedHeap = expand(postApp).map(ptss => ptss.subst(subst).pp)
        val expandedHeapStr = if (expandedHeap.nonEmpty) expandedHeap.mkString(" \\+ ") else "empty"
        builder.append(s"exists ($expandedHeapStr);\n")
      }

      builder.append("ssl_emp_post.\n")

      def expand2(app: CSApp): Unit = {
        val app1 = app.subst(subst).asInstanceOf[CSApp]
        val (expandedApp, clause) = heapSubst1(app1)
        val pred = predicates.find(_.name == clause.pred).get
        builder.append(s"constructor ${clause.idx + 1}=>//;\n")
        val valueEx = clause.asn.valueEx.filterNot(pred.params.map(_._2).contains).distinct.map(_.subst(subst).pp)
        if (valueEx.nonEmpty) {
          builder.append(s"exists ${valueEx.mkString(", ")};\n")
        }
        if (expandedApp.apps.nonEmpty) {
          val expandedHeap = expandedApp.apps.flatMap(expand)
          val expandedHeapStr = if (expandedHeap.nonEmpty) expandedHeap.map(_.pp).mkString(" \\+ ") else "empty"
          builder.append(s"exists $expandedHeapStr;\n")
        }
        builder.append("ssl_emp_post.\n")
        expandedApp.apps.foreach(expand2)
      }
      for (postApp <- postApps) {
        expand2(postApp)
      }

      builder.toString()
    }
  }
}
