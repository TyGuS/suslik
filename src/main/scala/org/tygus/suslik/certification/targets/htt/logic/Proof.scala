package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.CGamma
import org.tygus.suslik.certification.targets.htt.language.Expressions.{CExpr, CSApp, CSFormula, CSubst, CVar}
import org.tygus.suslik.certification.targets.htt.language.Types.{CUnitType, HTTType}
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CAssertion, CFunSpec}
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.language.PrettyPrinting

case class Proof(body: ProofTree[Proof.Step]) extends PrettyPrinting {
  override def pp: String = s"${ProofPrinter.pp(body)}Qed."
}

object Proof {
  case class Goal(pre: CAssertion,
                  post: CAssertion,
                  gamma: CGamma,
                  programVars: Seq[CVar],
                  universalGhosts: Seq[CVar],
                  fname: String) {
    val existentials: Seq[CVar] = post.valueVars.diff(programVars ++ universalGhosts)
    def subst(sub: CSubst): Goal = Goal(
      pre.subst(sub),
      post.subst(sub),
      gamma.map { case (v, t) => v.substVar(sub) -> t },
      programVars.map(_.substVar(sub)),
      universalGhosts.map(_.substVar(sub)),
      fname
    )

    def toFunspec: CFunSpec = {
      val params = programVars.map(v => (v, gamma(v)))
      val ghosts = universalGhosts.map(v => (v, gamma(v)))
      CFunSpec(fname, CUnitType, params, ghosts, pre, post)
    }
  }

  abstract class Step extends DestStep {
    val isNoop: Boolean = false
    def andThen: Step = Then(this)
  }

  case class Then(step: Step) extends Step {
    override val isNoop: Boolean = step.isNoop
    override def pp: String = step.pp
  }
  case class Rename(from: String, to: String) extends Step {
    override def pp: String = s"try rename $from into $to"
  }
  case class MoveToCtx(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    override def pp: String = s"move=>${items.map(_.pp).mkString(" ")}"
  }
  case class MoveToCtxDestruct(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    override def pp: String = s"move=>${items.map(i => s"[${i.pp}]").mkString(" ")}"
  }
  case class MoveToCtxDestructFoldLeft(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    override def pp: String = s"move=>${items.map(_.pp).reduceLeft[String]{ case (acc, el) => s"[$acc $el]"}}"
  }
  case class MoveToCtxDestructFoldRight(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    override def pp: String = s"move=>${items.map(_.pp).reduceRight[String]{ case (el, acc) => s"[$el $acc]"}}"
  }
  case class MoveToGoal(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    override def pp: String = s"move: ${items.map(_.pp).mkString(" ")}"
  }
  case class ElimExistential(items: Seq[CVar]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    override def pp: String = items.map(_.pp).grouped(5).map(s => s"ex_elim ${s.mkString(" ")}").mkString(".\n")
  }
  case class Sbst(vars: Seq[CVar]) extends Step {
    override def pp: String = if (vars.isEmpty) s"subst" else s"subst ${vars.map(_.pp).mkString(" ")}"
  }
  case class Exists(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    override def pp: String = s"exists ${items.map {
      case h:CSFormula => s"(${h.ppHeap})"
      case i => s"(${i.pp})"
    }.mkString(", ")}"
  }
  case object Auto extends Step {
    override def pp: String = "sslauto"
  }
  case class Close(idx: Int) extends Step {
    override def pp: String = s"ssl_close $idx"
  }
  case class Write(to: CVar, offset: Int = 0, e: CExpr) extends Step {
    override def pp: String = {
      val ptr = if (offset == 0) to.pp else s"(${to.pp} .+ $offset)"
      s"ssl_write $ptr"
    }
  }
  case class WritePost(to: CVar, offset: Int = 0) extends Step {
    override def pp: String = {
      val ptr = if (offset == 0) to.pp else s"(${to.pp} .+ $offset)"
      s"ssl_write_post $ptr"
    }
  }
  case class Read(to: CVar, from: CVar, offset: Int = 0) extends Step {
    override def pp: String = {
      val ptr = if (offset == 0) from.pp else s"(${from.pp} .+ $offset)"
      s"ssl_read $ptr"
    }
  }
  case class Alloc(to: CVar, tpe: HTTType, sz: Int) extends Step {
    override def pp: String = s"ssl_alloc ${to.pp}"
  }
  case class Dealloc(v: CVar, offset: Int) extends Step {
    override def pp: String = {
      val ptr = if (offset == 0) v.pp else s"(${v.pp} .+ $offset)"
      s"ssl_dealloc $ptr"
    }
  }
  case class Open(selectors: Seq[CExpr], app: CSApp) extends Step {
    override def pp: String = s"ssl_open (${selectors.head.pp}) ${app.hypName}"
  }
  case class CallPre(heap: CSFormula) extends Step {
    override def pp: String = s"ssl_call_pre (${heap.ppHeap})"
  }
  case class Call(ghosts: Seq[CExpr]) extends Step {
    override def pp: String = s"ssl_call (${ghosts.map(_.pp).mkString(", ")})"
  }
  case object StoreValid extends Step {
    override def pp: String = "store_valid"
  }
  case object GhostElimPre extends Step {
    override def pp: String = "ssl_ghostelim_pre"
  }
  case object GhostElimPost extends Step {
    override def pp: String = "ssl_ghostelim_post"
  }
  case class Branch(cond: CExpr) extends Step {
    override def pp: String = s"ssl_branch (${cond.pp})"
  }
  case object FrameUnfold extends Step {
    override def pp: String = "ssl_frame_unfold"
  }
  case object Emp extends Step {
    override def pp: String = "ssl_emp"
  }
  case object Inconsistency extends Step {
    override def pp: String = "ssl_inconsistency"
  }
  case class StartProof(params: Seq[CVar]) extends Step {
    override def pp: String = s"Obligation Tactic := intro; ${MoveToCtxDestructFoldLeft(params).pp}; ssl_program_simpl.\nNext Obligation"
  }
  case object EndProof extends Step {
    override def pp: String = "Qed.\n"
  }
  case object Shelve extends Step {
    override def pp: String = "shelve"
  }
  case object Unshelve extends Step {
    override def pp: String = "Unshelve"
  }
}
