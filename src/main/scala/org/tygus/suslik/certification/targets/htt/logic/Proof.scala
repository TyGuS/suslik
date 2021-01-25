package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.Expressions.{CExpr, CSApp, CSFormula, CVar}
import org.tygus.suslik.certification.targets.htt.language.Types.HTTType

object Proof {
  abstract class Step {
    val isNoop: Boolean = false
    def pp: String
    def >>(that: Step): Step = SeqComp(this, that)
    def >>>(that: Step): Step = SeqCompAlt(this, that)
    def simplify: Step = this match {
      case SeqComp(s1, s2) => if (s1.isNoop) s2.simplify else if (s2.isNoop) s1.simplify else SeqComp(s1.simplify, s2.simplify)
      case SeqCompAlt(s1, s2) => if (s1.isNoop) s2.simplify else if (s2.isNoop) s1.simplify else SeqCompAlt(s1.simplify, s2.simplify)
      case SubProof(branches) => SubProof(branches.filterNot(_.isNoop).map(_.simplify))
      case Solve(steps) => Solve(steps.filterNot(_.isNoop).map(_.simplify))
      case _ => this
    }
  }

  case class SubProof(branches: Seq[Step]) extends Step {
    override val isNoop: Boolean = branches.forall(_.isNoop)
    def pp: String = branches.map(_.pp).mkString(".\n")
  }
  case class SeqComp(s1: Step, s2: Step) extends Step {
    override val isNoop: Boolean = s1.isNoop && s2.isNoop
    def pp: String = s"${s1.pp}.\n${s2.pp}"
  }
  case class SeqCompAlt(s1: Step, s2: Step) extends Step {
    override val isNoop: Boolean = s1.isNoop && s2.isNoop
    def pp: String = s"${s1.pp};\n${s2.pp}"
  }
  case class Solve(steps: Seq[Step]) extends Step {
    override val isNoop: Boolean = steps.forall(_.isNoop)
    def pp: String = s"solve [\n${steps.map(_.pp).mkString(" |\n")} ]"
  }
  case class MoveToCtx(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    def pp: String = s"move=>${items.map(_.pp).mkString(" ")}"
  }
  case class MoveToCtxDestruct(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    def pp: String = s"move=>${items.map(i => s"[${i.pp}]").mkString(" ")}"
  }
  case class MoveToCtxDestructFoldLeft(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    def pp: String = s"move=>${items.map(_.pp).reduceLeft[String]{ case (acc, el) => s"[$acc $el]"}}"
  }
  case class MoveToCtxDestructFoldRight(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    def pp: String = s"move=>${items.map(_.pp).reduceRight[String]{ case (el, acc) => s"[$el $acc]"}}"
  }
  case class MoveToGoal(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    def pp: String = s"move: ${items.map(_.pp).mkString(" ")}"
  }
  case class ElimExistential(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    def pp: String = items.map(_.pp).grouped(5).map(s => s"ex_elim ${s.mkString(" ")}").mkString(".\n")
  }
  case class Sbst(vars: Seq[CVar]) extends Step {
    def pp: String = if (vars.isEmpty) s"subst" else s"subst ${vars.map(_.pp).mkString(" ")}"
  }
  case class Exists(items: Seq[CExpr]) extends Step {
    override val isNoop: Boolean = items.isEmpty
    def pp: String = s"exists ${items.map {
      case h:CSFormula => s"(${h.ppHeap})"
      case i => s"(${i.pp})"
    }.mkString(", ")}"
  }
  case object Auto extends Step {
    def pp: String = "sslauto"
  }
  case class UnfoldConstructor(idx: Int) extends Step {
    def pp: String = s"unfold_constructor $idx"
  }
  case class Write(to: CVar, offset: Int = 0, e: CExpr) extends Step {
    def pp: String = {
      val ptr = if (offset == 0) to.pp else s"(${to.pp} .+ $offset)"
      s"ssl_write $ptr"
    }
  }
  case class WritePost(to: CVar, offset: Int = 0) extends Step {
    def pp: String = {
      val ptr = if (offset == 0) to.pp else s"(${to.pp} .+ $offset)"
      s"ssl_write_post $ptr"
    }
  }
  case class Read(to: CVar, from: CVar, offset: Int = 0) extends Step {
    def pp: String = {
      val ptr = if (offset == 0) from.pp else s"(${from.pp} .+ $offset)"
      s"ssl_read $ptr"
    }
  }
  case class Alloc(to: CVar, tpe: HTTType, sz: Int) extends Step {
    def pp: String = s"ssl_alloc ${to.pp}"
  }
  case class Dealloc(v: CVar, offset: Int) extends Step {
    def pp: String = {
      val ptr = if (offset == 0) v.pp else s"(${v.pp} .+ $offset)"
      s"ssl_dealloc $ptr"
    }
  }
  case class Open(selectors: Seq[CExpr]) extends Step {
    def pp: String = s"ssl_open (${selectors.head.pp})"
  }
  case class OpenPost(app: CSApp) extends Step {
    def pp: String = s"ssl_open_post ${app.hypName}"
  }
  case class CallPre(heap: CSFormula) extends Step {
    def pp: String = s"ssl_call_pre (${heap.ppHeap})"
  }
  case class Call(args: Seq[CExpr], ghosts: Seq[CVar]) extends Step {
    def pp: String = s"ssl_call (${ghosts.map(_.pp).mkString(", ")})"
  }
  case object StoreValid extends Step {
    def pp: String = "store_valid"
  }
  case object GhostElimPre extends Step {
    def pp: String = "ssl_ghostelim_pre"
  }
  case object GhostElimPost extends Step {
    def pp: String = "ssl_ghostelim_post"
  }
  case class Branch(cond: CExpr) extends Step {
    def pp: String = s"ssl_abduce_branch (${cond.pp})"
  }
  case object Emp extends Step {
    def pp: String = "ssl_emp"
  }
  case object Error extends Step {
    override val isNoop: Boolean = true
    def pp: String = ""
  }
  case object Noop extends Step {
    override val isNoop: Boolean = true
    def pp: String = ""
  }
  case class StartProof(params: Seq[CVar]) extends Step {
    def pp: String = s"Obligation Tactic := intro; ${MoveToCtxDestructFoldLeft(params).pp}; ssl_program_simpl.\nNext Obligation"
  }
  case object EndProof extends Step {
    def pp: String = "Qed.\n"
  }
}
