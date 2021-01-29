package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.{ProofTree, SuslikProofStep}
import org.tygus.suslik.certification.targets.htt.language.CGamma
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CAssertion, CFunSpec, CInductiveClause, CInductivePredicate}
import org.tygus.suslik.certification.targets.htt.program.Statements._
import org.tygus.suslik.certification.targets.htt.translation.Translation.{translateAsn, translateExpr, translateParam, translateSApp, translateType, translateVar}
import org.tygus.suslik.language.Expressions.{Subst, SubstVar, Var}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.language.Statements.{Call, Free, Load, Malloc, Store}
import org.tygus.suslik.logic.{FunSpec, Gamma}
import org.tygus.suslik.logic.Specifications.Goal

object IR {
  type Unfoldings = Map[CSApp, CInductiveClause]
  type SAppNames = Map[CSApp, String]
  type CSubst = Map[CVar, CExpr]
  type CSubstVar = Map[CVar, CVar]
  type PredicateEnv = Map[String, CInductivePredicate]

  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: CGamma,
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String) {
    val existentials: Seq[CVar] = post.valueVars.diff(programVars ++ universalGhosts)
    def subst(sub: CSubst): CGoal = CGoal(
      pre.subst(sub),
      post.subst(sub),
      gamma.map { case (v, t) => v.substVar(sub) -> t },
      programVars.map(_.substVar(sub)),
      universalGhosts.map(_.substVar(sub)),
      fname
    )

    def toFunspec: CFunSpec = {
      val params = programVars.map(v => (gamma(v), v))
      val ghosts = universalGhosts.map(v => (gamma(v), v))
      CFunSpec(fname, CUnitType, params, ghosts, pre, post)
    }
  }

  case class Context(
                      unfoldings: Unfoldings,
                      sappNames: SAppNames,
                      subst: CSubst,
                      substVar: CSubstVar,
                      predicateEnv: PredicateEnv,
                      nestedContext: Option[NestedContext],
                      topLevelGoal: Option[CGoal],
                    )

  val emptyContext: Context = Context(Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, None, None)

  case class NestedContext(funspec: CFunSpec, call: CCall, freshToActual: CSubst = Map.empty, companionToFresh: CSubstVar) {
    def updateSubstitution(sigma: CSubst): NestedContext = {
      this.copy(freshToActual = freshToActual.map { case (k, e) => k -> e.subst(sigma) } ++ sigma)
    }

    def applySubstitution: NestedContext = {
      val newPost = funspec.post.subst(freshToActual)
      val newFunSpec = funspec.copy(post = newPost)
      val newCall = call.copy(args = call.args.map(_.subst(freshToActual)))
      this.copy(funspec = newFunSpec, call = newCall)
    }
  }

  abstract class Node {
    val ctx : Context
    val next : Seq[Node]

    def propagateContext: IR.Node = this match {
      case n:IR.EmpRule => n
      case n:IR.Open => n.copy(next = n.next.map(_.propagateContext))
      case n:IR.AbduceBranch =>n.copy(next = n.next.map(_.propagateContext))
      case n:IR.Read =>
        val next1 = n.next.head.propagateContext
        n.copy(ctx = next1.ctx, next = Seq(next1))
      case n:IR.Call =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Free =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Write =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Malloc =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.PureSynthesis =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Close =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.AbduceCall =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Init =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.CheckPost =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Inconsistency => n
    }
  }

  case class Open(app: CSApp, clauses: Seq[CInductiveClause], selectors: Seq[CExpr], next: Seq[Node], ctx: Context) extends Node

  case class Close(app: CSApp, selector: CExpr, asn: CAssertion, fresh_exist: CSubstVar, next: Seq[Node], ctx: Context) extends Node

  case class AbduceBranch(cond: CExpr, next: Seq[Node], ctx: Context) extends Node

  case class PureSynthesis(is_final: Boolean, next: Seq[Node], ctx: Context) extends Node

  case class Read(op: CLoad, next: Seq[Node], ctx: Context) extends Node

  case class Write(stmt: CStore, next: Seq[Node], ctx: Context) extends Node

  case class Free(stmt: CFree, next: Seq[Node], ctx: Context) extends Node

  case class Malloc(stmt: CMalloc, next: Seq[Node], ctx: Context) extends Node

  case class AbduceCall(new_vars: Map[CVar, HTTType],
                        f_pre: CAssertion,
                        calleePost: CAssertion,
                        call: CCall,
                        freshSub: CSubstVar,
                        freshToActual: CSubst,
                        next: Seq[Node],
                        ctx: Context
                       ) extends Node

  case class Call(call: CCall, next: Seq[Node], ctx: Context) extends Node

  case class EmpRule(ctx: Context) extends Node {
    val next: Seq[Node] = Seq.empty
  }

  case class Init(ctx: Context, next: Seq[Node]) extends Node

  case class Inconsistency(ctx: Context) extends Node {
    val next: Seq[Node] = Seq.empty
  }

  case class CheckPost(prePhi: Set[CExpr], postPhi: Set[CExpr], next: Seq[Node], ctx: Context) extends Node

  private def translateSbst(sbst: Subst) = sbst.map{ case (k,v) => CVar(k.name) -> translateExpr(v)}
  private def translateSbstVar(sbst: SubstVar) = sbst.map{ case (k,v) => CVar(k.name) -> CVar(v.name)}
  def translateGoal(goal: Goal): CGoal = {
    val pre = translateAsn(goal.pre)
    val post = translateAsn(goal.post)
    val gamma = goal.gamma.map { case (value, lType) => (translateVar(value), translateType(lType)) }
    val programVars = goal.programVars.map(translateVar)
    val universalGhosts = (pre.valueVars ++ post.valueVars).distinct.filter(v => goal.universalGhosts.contains(Var(v.name)))
    CGoal(pre, post, gamma, programVars, universalGhosts, goal.fname)
  }
  def translateFunSpec(f: FunSpec, gamma: Gamma): CFunSpec = {
    val rType = translateType(f.rType)
    val pre = translateAsn(f.pre)
    val post = translateAsn(f.post)
    val params = f.params.map(translateParam)
    val ghosts = pre.valueVars.diff(params.map(_._2)).map(v => (translateType(gamma(Var(v.name))), v))
    CFunSpec(f.name, rType, params, ghosts, pre, post)
  }

  def fromRule(rule: ProofTree[SuslikProofStep], ctx: IR.Context) : IR.Node = rule match {
    case ProofTree(SuslikProofStep.Init(goal), List(next)) =>
      val cgoal = translateGoal(goal)
      val ctx1 = ctx.copy(topLevelGoal = Some(cgoal))
      IR.Init(ctx1, Seq(fromRule(next, ctx1)))
    case ProofTree(SuslikProofStep.Open(sapp, fresh_vars, sbst, cases), children) =>
      val csapp = translateSApp(sapp)
      val freshCVars = fresh_vars.map{ case (k,v) => CVar(k.name) -> translateExpr(v)}
      val csbst = translateSbst(sbst)
      val pred = ctx.predicateEnv(sapp.pred).subst(freshCVars).subst(csbst)
      val (selectors, next) = cases.zip(children).map{ case (s, r) => (translateExpr(s), fromRule(r, ctx)) }.unzip
      IR.Open(csapp, pred.clauses, selectors, next, ctx)
    case ProofTree(SuslikProofStep.Close(sapp, selector, asn, sbst), List(next)) =>
      val csapp = translateSApp(sapp)
      val cselector = translateExpr(selector)
      val casn = translateAsn(asn)
      val csbst = translateSbst(sbst)
      val pred = ctx.predicateEnv(csapp.pred)
      val cclause = pred.clauses.find(_.selector == cselector).get
      val ex = cclause.existentials.map(_.subst(csbst))
      val actualClause = CInductiveClause(csapp.pred, cclause.idx, cselector, casn, ex)
      fromRule(next, ctx.copy(unfoldings = ctx.unfoldings + (csapp -> actualClause)))
    case ProofTree(SuslikProofStep.AbduceBranch(cond), List(ifTrue, ifFalse)) =>
      IR.AbduceBranch(translateExpr(cond), Seq(fromRule(ifTrue, ctx), fromRule(ifFalse, ctx)), ctx)
    case ProofTree(SuslikProofStep.PureSynthesis(is_final, sbst), List(next)) =>
      val csbst = translateSbst(sbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst)))
      IR.PureSynthesis(is_final, Seq(fromRule(next, ctx1)), ctx1)
    case ProofTree(SuslikProofStep.SubstL(sbst), List(next)) =>
      val csbst = translateSbst(sbst)
      fromRule(next, ctx.copy(subst = ctx.subst ++ csbst))
    case ProofTree(SuslikProofStep.SubstR(sbst), List(next)) =>
      val csbst = translateSbst(sbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst)))
      fromRule(next, ctx1)
    case ProofTree(SuslikProofStep.Pick(sbst), List(next)) =>
      val csbst = translateSbst(sbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst)))
      fromRule(next, ctx1)
    case ProofTree(SuslikProofStep.Read(ghosts, Load(to, tpe, from, offset)), List(next)) =>
      val ctx1 = ctx.copy(substVar = ctx.substVar ++ translateSbstVar(ghosts))
      IR.Read(CLoad(CVar(to.name), translateType(tpe), CVar(from.name), offset), Seq(fromRule(next, ctx1)), ctx1)
    case ProofTree(SuslikProofStep.Write(Store(to, offset, e)), List(next)) =>
      IR.Write(CStore(CVar(to.name), offset, translateExpr(e)), Seq(fromRule(next, ctx)), ctx)
    case ProofTree(SuslikProofStep.Free(Statements.Free(v), size), List(next)) =>
      IR.Free(CFree(CVar(v.name), size), Seq(fromRule(next, ctx)), ctx)
    case ProofTree(SuslikProofStep.Malloc(ghosts, Statements.Malloc(to, tpe, sz)), List(next)) =>
      val ctx1 = ctx.copy(substVar = ctx.substVar ++ translateSbstVar(ghosts))
      IR.Malloc(CMalloc(CVar(to.name), translateType(tpe), sz), Seq(fromRule(next, ctx1)), ctx1)
    case ProofTree(SuslikProofStep.Call(_, Statements.Call(fun, args, _)), List(next)) =>
      val ctx1 = ctx.copy(nestedContext = ctx.nestedContext.map(_.applySubstitution))
      val ctx2 = ctx1.copy(nestedContext = None)
      IR.Call(CCall(CVar(fun.name), args.map(translateExpr)), Seq(fromRule(next, ctx2)), ctx1)
    case ProofTree(SuslikProofStep.PickArg(sbst), List(next)) =>
      val csbst = translateSbst(sbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst)))
      fromRule(next, ctx1)
    case ProofTree(SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, companionToFresh, freshToActual, f, gamma), List(next)) =>
      val cfunspec = translateFunSpec(f, gamma)
      val ccall = CCall(translateVar(call.fun), call.args.map(translateExpr))
      val nestedContext = NestedContext(funspec = cfunspec, call = ccall, freshToActual = translateSbst(freshToActual), companionToFresh = translateSbstVar(companionToFresh))
      val ctx1 = ctx.copy(nestedContext = Some(nestedContext))
      fromRule(next, ctx1)
    case ProofTree(SuslikProofStep.HeapUnifyPointer(sbst), List(next)) =>
      val ctx1 = ctx.copy(subst = ctx.subst ++ translateSbst(sbst))
      fromRule(next, ctx1)
    case ProofTree(SuslikProofStep.EmpRule, List()) => IR.EmpRule(ctx)
    case ProofTree(SuslikProofStep.CheckPost(prePhi, postPhi), List(next)) =>
      IR.CheckPost(prePhi.conjuncts.map(translateExpr), postPhi.conjuncts.map(translateExpr), Seq(fromRule(next, ctx)), ctx)
    // unused rules:
    case ProofTree(SuslikProofStep.HeapUnify(_), List(next)) => fromRule(next, ctx)
    case ProofTree(SuslikProofStep.NilNotLval(_), List(next)) => fromRule(next, ctx)
    case ProofTree(SuslikProofStep.WeakenPre(_), List(next)) => fromRule(next, ctx)
    case ProofTree(SuslikProofStep.StarPartial(_, _), List(next)) => fromRule(next, ctx)
    case ProofTree(SuslikProofStep.PickCard(_), List(next)) => fromRule(next, ctx)
    case ProofTree(SuslikProofStep.FrameUnfold(h_pre, h_post), List(next)) => fromRule(next, ctx)
    case ProofTree(SuslikProofStep.Inconsistency, List()) => IR.Inconsistency(ctx)
  }
}
