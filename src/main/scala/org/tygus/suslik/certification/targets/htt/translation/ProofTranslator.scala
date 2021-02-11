package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.language.Expressions.CVar
import org.tygus.suslik.certification.targets.htt.logic.Proof
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CAssertion, CInductiveClause}
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Evaluator.Deferreds
import org.tygus.suslik.certification.traversal.Translator
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.language.Statements._

import scala.collection.immutable.Queue

object ProofTranslator extends Translator[SuslikProofStep, Proof.Step, Context] {
  private val noDeferreds: Deferreds[Proof.Step, Context] = Queue.empty
  private def withNoDeferreds(ctx: Context): (Deferreds[Proof.Step, Context], Context) = (noDeferreds, ctx)

  private def initPre(asn: CAssertion, uniqueName: String): List[Proof.Step] = {
    val phi = asn.phi
    val sigma = asn.sigma

    // move pure part to context
    val pureToCtx = if (!phi.isTrivial) {
      val hyps = if (phi.conjuncts.isEmpty) Seq(CVar(s"phi_$uniqueName")) else phi.conjuncts.indices.map(i => CVar(s"phi_$uniqueName$i"))
      List(Proof.MoveToCtxDestruct(hyps))
    } else Nil

    // move spatial part to context, and then substitute where appropriate
    val spatialToCtx = List(
      Proof.MoveToCtxDestruct(Seq(CVar(s"sigma_$uniqueName"))),
      Proof.Sbst(Seq(CVar(s"h_$uniqueName")))
    )

    // move predicate apps to context, if any
    val sappToCtx = if (sigma.apps.nonEmpty) {
      val appNames = sigma.apps.map(app => CVar(app.hypName))
      List(Proof.MoveToCtxDestructFoldRight(appNames))
    } else Nil

    pureToCtx ++ spatialToCtx ++ sappToCtx
  }

  override def translate(value: SuslikProofStep, ctx: Context): Translator.Result[Proof.Step, Context] = {
    value match {
      /** Initialization */
      case SuslikProofStep.Init(goal) =>
        val programVars = goal.programVars.map(_.translate)
        val universalGhosts = goal.universalGhosts.map(_.translate).toSeq

        // handle pre-condition immediately
        val pre = goal.pre.translate
        val steps = List(
          Proof.StartProof(programVars),
          Proof.GhostElimPre,
          Proof.MoveToCtxDestructFoldLeft(universalGhosts),
          Proof.ElimExistential(pre.heapVars)
        ) ++ initPre(pre, "self") ++ List(Proof.GhostElimPost)

        // defer post-condition handling
        val post = goal.post.translate
        val sapps = post.sigma.apps
        val d1 = (ctx: Context) => (Proof.Exists(ctx.postEx) andThen, ctx)
        val q0 = sapps.foldLeft(Queue(d1)) { case (q, app) =>
          val d = (ctx: Context) => {
            val app1 = ctx.currentAppAlias(app)
            val heap = ctx.unfoldedApp(app1)
            (Proof.Exists(List(heap)) andThen, ctx)
          }
          q.enqueue(d)
        }
        val d2 = (ctx: Context) => (Proof.Auto, ctx)
        val q = q0.enqueue(d2)

        // initialize context with post-condition info
        val postEx = post.valueVars.diff(programVars ++ universalGhosts)
        val appAliases = sapps.map(a => a -> a).toMap
        val ctx1 = ctx.copy(postEx = postEx, appAliases = appAliases)

        Result(steps, List((q, ctx1)))

      /** Control flow */
      case SuslikProofStep.Branch(cond, _) =>
        val meta = withNoDeferreds(ctx)
        Result(List(Proof.Branch(cond.translate)), List(meta, meta))
      case SuslikProofStep.Open(sapp, fresh_vars, sbst, selectors) =>
        val pred = ctx.predicates(sapp.pred).subst(fresh_vars.translate).subst(sbst.translate)
        val csapp = sapp.translate
        val cselectors = selectors.map(_.translate)
        val branchSteps = pred.clauses.flatMap { clause =>
          List(
            Proof.ElimExistential(clause.existentials),
            Proof.ElimExistential(clause.asn.heapVars)
          ) ++ initPre(clause.asn, csapp.uniqueName) ++ List(Proof.Shelve)
        }
        val steps = List(Proof.Open(cselectors), Proof.OpenPost(csapp)) ++ branchSteps ++ List(Proof.Unshelve)
        Result(steps, selectors.map(_ => withNoDeferreds(ctx)))

      /** Program statements */
      case SuslikProofStep.Read(ghostFrom, ghostTo, Load(to, _, from, offset)) =>
        val readStep = Proof.Read(to.translate, from.translate, offset)
        val renameStep = Proof.Rename(ghostFrom.translate, ghostTo.translate)
        val ctx1 = ctx.withRename(ghostFrom.translate, ghostTo.translate)
        Result(List(readStep, renameStep), List(withNoDeferreds(ctx1)))
      case SuslikProofStep.Write(Store(to, offset, e)) =>
        val writeStep = Proof.Write(to.translate, offset, e.translate)
        val writePostStep = Proof.WritePost(to.translate, offset)
        Result(List(writeStep, writePostStep), List(withNoDeferreds(ctx)))
      case SuslikProofStep.Malloc(ghostFrom, ghostTo, Malloc(to, tpe, sz)) =>
        val allocStep = Proof.Alloc(to.translate, tpe.translate, sz)
        val renameStep = Proof.Rename(ghostFrom.translate, ghostTo.translate)
        val ctx1 = ctx.withRename(ghostFrom.translate, ghostTo.translate)
        Result(List(allocStep, renameStep), List(withNoDeferreds(ctx1)))
      case SuslikProofStep.Free(Free(v), size) =>
        val steps = (0 until size).map(i => Proof.Dealloc(v.translate, i)).toList
        Result(steps, List(withNoDeferreds(ctx)))
      case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) =>
        ??? // TODO
      case SuslikProofStep.Call(subst, call) =>
        ??? // TODO

      //      case SuslikProofStep.CheckPost(prePhi, postPhi) => ??? TODO: collect pure entailments

      /** Substitutions and unfoldings */
      case SuslikProofStep.Pick(from, to) =>
        val ctx1 = ctx.withSubst(Map(from.translate -> to.translate))
        Result(List(Proof.Noop), List(withNoDeferreds(ctx1)))
      case SuslikProofStep.PickArg(from, to) =>
        val ctx1 = ctx.withRename(from.translate, to.translate)
        Result(List(Proof.Rename(from.translate, to.translate)), List(withNoDeferreds(ctx1)))
      case SuslikProofStep.PureSynthesis(_, assignments) =>
        val ctx1 = ctx.withSubst(assignments.translate)
        Result(List(Proof.Noop), List(withNoDeferreds(ctx1)))
      case SuslikProofStep.SubstL(from, to) =>
        val ctx1 = ctx.withSubst(Map(from.translate -> to.translate))
        Result(List(Proof.Noop), List(withNoDeferreds(ctx1)))
      case SuslikProofStep.SubstR(from, to) =>
        val ctx1 = ctx.withSubst(Map(from.translate -> to.translate))
        Result(List(Proof.Noop), List(withNoDeferreds(ctx1)))
      case SuslikProofStep.Close(app, selector, asn, fresh_exist) =>
        // construct an up-to-date inductive clause with synthesis info
        val csapp = app.translate
        val cselector = selector.translate
        val m = fresh_exist.translate
        val clause0 = ctx.predicates(csapp.pred).clauses.find(_.selector == cselector).get
        val clause = CInductiveClause(csapp.pred, clause0.idx, cselector, asn.translate, clause0.existentials.map(_.subst(m)))

        // create deferreds to perform unfolding
        val deferreds = Queue(
          (ctx: Context) => (Proof.UnfoldConstructor(clause.idx), ctx),
          (ctx: Context) => {
            val csapp1 = ctx.currentAppAlias(csapp)
            val (valueEx, heapEx) = ctx.unfoldedAppExistentials(csapp1)
            (Proof.Exists(valueEx ++ heapEx), ctx)
          },
          (ctx: Context) => (Proof.Auto, ctx)
        )

        // update context with unfolding info
        val appAliases = ctx.appAliases ++ clause.asn.sigma.apps.map(a => a -> a)
        val unfoldings = ctx.unfoldings + (csapp -> clause)
        val ctx1 = ctx.copy(appAliases = appAliases, unfoldings = unfoldings)

        Result(List(Proof.Noop), List((deferreds, ctx1)))

      /** Terminals */
      case SuslikProofStep.Inconsistency(label) =>
        Result(List(Proof.Error), Nil)
      case SuslikProofStep.EmpRule(label) =>
        Result(List(Proof.Emp andThen), Nil)

      /** Ignored */
      case _ => Result(List(Proof.Noop), List(withNoDeferreds(ctx)))
    }
  }
}
