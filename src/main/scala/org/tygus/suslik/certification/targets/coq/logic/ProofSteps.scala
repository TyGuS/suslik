package org.tygus.suslik.certification.targets.coq.logic

import org.tygus.suslik.certification.targets.coq.language._
import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.logic.Proof.CGoal

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
        case WriteStep(to) =>
          acc ++ to.collect(p)
        case ReadStep(to) =>
          acc ++ to.collect(p)
        case AllocStep(to, _, _) =>
          acc ++ to.collect(p)
        case SeqCompStep(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case CallStep(app, _) =>
          val argVars = app.args.flatMap(arg => arg.collect(p)).toSet
          acc ++ argVars
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
        case (WriteStep(to), _) => simplifyBinding(to)
        case (AllocStep(to, _, _), _) => simplifyBinding(to)
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

  case class WriteStep(to: CVar) extends ProofStep {
    override def pp: String = s"ssl_write.\nssl_write_post ${to.pp}.\n"
  }

  case class ReadStep(to: CVar) extends ProofStep {
    override def pp: String = "ssl_read.\n"
  }

  case class AllocStep(to: CVar, tpe: CoqType, sz: Int) extends ProofStep {
    override def pp: String = s"ssl_alloc $to.\n"
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

  case class OpenPostStep(app: CSApp, pred: CInductivePredicate, clause: CInductiveClause, goal: CGoal) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()
      builder.append(s"case ${app.hypName}; rewrite H_cond=>//= _.\n")

      val asn = clause.asn
      val subst = goal.pre.unify(asn)
      val ve0 = (asn.spatialEx ++ asn.pureEx).diff(pred.params.map(_._2)).distinct
      val ve = ve0.map(subst(_))
      val ptss = asn.sigma.ptss
      val apps = asn.sigma.apps

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
        builder.append("move=>H_valid.\n")
      }

      builder.toString()
    }
  }

  case object AbduceBranchStep extends ProofStep {
    override def pp: String = "case: ifP=>H_cond.\n"
  }

  case class EmpStep(spec: CFunSpec) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()
      builder.append("ssl_emp;\n")


      // instantiate any existentials from the fun spec post
      val post = spec.post
      val programVars = spec.programVars
      val ve = (post.spatialEx ++ post.pureEx).diff(programVars).distinct

//      if (ve.nonEmpty) {
//        val subs = ve.map(e => {
//          // first, see if it matches any existentials produced by the Pick rule
//          env.existentials.get(e) match {
//            case Some(v) => v.pp
//            case None =>
//            // if that doesn't work, match from the unrolled predicates
//
//          }
//        })
//        builder.append(s"exists ${subs.mkString(", ")};\n")
//      }

      builder.append("ssl_emp_post.\n")

      builder.toString()
    }
  }
}
