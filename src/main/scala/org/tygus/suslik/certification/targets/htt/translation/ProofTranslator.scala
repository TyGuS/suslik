package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.language.Expressions.{CExpr, CSApp, CVar}
import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CAssertion, CInductiveClause}
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Evaluator.Deferreds
import org.tygus.suslik.certification.traversal.Translator
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.language.Statements.{Call, Free, Load, Malloc, Store}

import scala.collection.immutable.Queue

object ProofTranslator extends Translator[SuslikProofStep, Proof.Step, ProofContext] {
  private val noDeferreds: Deferreds[Proof.Step, ProofContext] = Queue.empty
  private def withNoDeferreds(ctx: ProofContext): (Deferreds[Proof.Step, ProofContext], ProofContext) = (noDeferreds, ctx)

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

  def renameAppsStep(affectedApps: Map[CSApp, CSApp]): List[Proof.Rename] = {
    for {
      (appBefore, appAfter) <- affectedApps.toList
      (from, to) <- Map(appBefore.heapName -> appAfter.heapName, appBefore.hypName -> appAfter.hypName)
    } yield Proof.Rename(from, to)
  }

  def handleSubstitution(m: Map[CVar, CExpr], ctx: ProofContext): Translator.Result[Proof.Step, ProofContext] = {
    val affectedApps = ctx.appsAffectedBySubst(m)
    val ctx1 = ctx.withSubst(m, affectedApps)
    val steps = Proof.Noop :: renameAppsStep(affectedApps)
    Result(steps, List(withNoDeferreds(ctx1)))
  }

  override def translate(value: SuslikProofStep, ctx: ProofContext): Translator.Result[Proof.Step, ProofContext] = {
    value match {
      /** Initialization */
      case SuslikProofStep.Init(goal) =>
        val cgoal = goal.translate

        // handle pre-condition immediately
        val steps = List(
          Proof.StartProof(cgoal.programVars),
          Proof.GhostElimPre,
          Proof.MoveToCtxDestructFoldLeft(cgoal.universalGhosts),
          Proof.ElimExistential(cgoal.pre.heapVars)
        ) ++ initPre(cgoal.pre, "self") ++ List(Proof.GhostElimPost)

        // defer post-condition handling
        val sapps = cgoal.post.sigma.apps
        val d1 = (ctx: ProofContext) => (Proof.Exists(ctx.postEx) andThen, ctx)
        val q0 = sapps.foldLeft(Queue(d1)) { case (q, app) =>
          val d = (ctx: ProofContext) => {
            val app1 = ctx.currentAppAlias(app)
            val heap = ctx.unfoldedApp(app1)
            (Proof.Exists(List(heap)) andThen, ctx)
          }
          q.enqueue(d)
        }
        val d2 = (ctx: ProofContext) => (Proof.Auto, ctx)
        val q = q0.enqueue(d2)

        // initialize context with post-condition info and predicate hints, if any
        val appAliases = (cgoal.pre.sigma.apps ++ cgoal.post.sigma.apps).map(a => a -> a).toMap
        ctx.hints ++= ctx.predicates.values.map(p => Hint.PredicateSetTransitive(p))
        val ctx1 = ctx.copy(postEx = cgoal.existentials, appAliases = appAliases)

        Result(steps, List((q, ctx1)))
      case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) =>
        val pre = f.pre.translate
        val post = f.post.translate
        val programVars = f.params.map(_._1.translate)
        val universalGhosts = pre.valueVars.diff(programVars)
        val goal = Proof.Goal(pre, post, gamma.translate, programVars, universalGhosts, f.name)
        val ctx1 = ctx.copy(callGoal = Some(goal))
        Result(List(Proof.Noop), List(withNoDeferreds(ctx1)))

      /** Control flow */
      case SuslikProofStep.Branch(cond, _) =>
        val childContexts = List(ctx.copy(numSubgoals = ctx.numSubgoals + 1), ctx)
        Result(List(Proof.Branch(cond.translate)), childContexts.map(withNoDeferreds))
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
        val parentGoalShelves = (1 to ctx.numSubgoals).map(_ => Proof.Shelve).toList
        val steps = List(Proof.Open(cselectors, csapp)) ++ branchSteps ++ parentGoalShelves ++ List(Proof.Unshelve)

        val numClauses = pred.clauses.length
        val childCtxs = pred.clauses.toList.map(clause => {
          val newApps = clause.asn.sigma.apps.map(a => a -> a).toMap
          val numSubgoals = numClauses - clause.idx + ctx.numSubgoals
          ctx.copy(appAliases = ctx.appAliases ++ newApps, numSubgoals = numSubgoals)
        })
        Result(steps, childCtxs.map(withNoDeferreds))

      /** Program statements */
      case SuslikProofStep.Read(ghostFrom, ghostTo, Load(to, _, from, offset)) =>
        val readStep = Proof.Read(to.translate, from.translate, offset)
        val renameStep = Proof.Rename(ghostFrom.name, ghostTo.name)
        val m = Map(ghostFrom.translate -> ghostTo.translate)
        val affectedApps = ctx.appsAffectedBySubst(m)
        val ctx1 = ctx.withSubst(m, affectedApps)
        val steps = readStep :: renameStep :: renameAppsStep(affectedApps)
        Result(steps, List(withNoDeferreds(ctx1)))
      case SuslikProofStep.Write(Store(to, offset, e)) =>
        val writeStep = Proof.Write(to.translate, offset, e.translate)
        val writePostStep = Proof.WritePost(to.translate, offset)
        val steps = if (ctx.callGoal.isDefined) List(writeStep) else List(writeStep, writePostStep)
        Result(steps, List(withNoDeferreds(ctx)))
      case SuslikProofStep.Malloc(ghostFrom, ghostTo, Malloc(to, tpe, sz)) =>
        val allocStep = Proof.Alloc(to.translate, tpe.translate, sz)
        val renameStep = Proof.Rename(ghostFrom.name, ghostTo.name)
        val m = Map(ghostFrom.translate -> ghostTo.translate)
        val affectedApps = ctx.appsAffectedBySubst(m)
        val ctx1 = ctx.withSubst(m, affectedApps)
        val steps = allocStep :: renameStep :: renameAppsStep(affectedApps)
        Result(steps, List(withNoDeferreds(ctx1)))
      case SuslikProofStep.Free(Free(v), size) =>
        val steps = (0 until size).map(i => Proof.Dealloc(v.translate, i)).toList
        Result(steps, List(withNoDeferreds(ctx)))
      case SuslikProofStep.Call(freshToActual, Call(_, args, _)) =>
        val callId = ctx.nextCallId
        val callGoal = ctx.callGoal.get
        val goal = callGoal.subst(freshToActual.translate)

        val steps = List(
          // Move the part of the heap relevant to the call abduction to the beginning
          Proof.CallPre(goal.pre.sigma),
          // Provide the necessary existentials so that the precondition of the call goal is met,
          // and then execute the call
          Proof.Call(args.map(_.translate), goal.universalGhosts.filterNot(_.isCard)),
          Proof.Exists(goal.pre.sigma.apps.map(ctx.currentAppAlias).map(ctx.unfoldedApp)) andThen,
          Proof.Auto,
          Proof.MoveToCtx(List(CVar(s"h_call$callId"))),
          // The postcondition of the call abduction becomes the precondition of the companion
          Proof.ElimExistential(goal.existentials),
          Proof.ElimExistential(goal.post.heapVars),
        ) ++ initPre(goal.post, s"call$callId") ++ List(Proof.StoreValid)

        val newApps = goal.post.sigma.apps.map(a => a -> a).toMap
        val ctx1 = ctx.copy(callGoal = None, nextCallId = callId + 1, appAliases = ctx.appAliases ++ newApps)

        Result(steps, List(withNoDeferreds(ctx1)))

      /** Substitutions and unfoldings */
      case SuslikProofStep.Pick(from, to) =>
        val m = Map(from.translate -> to.translate)
        handleSubstitution(m, ctx)
      case SuslikProofStep.PickArg(from, to) =>
        val m = Map(from.translate -> to.translate)
        handleSubstitution(m, ctx)
      case SuslikProofStep.PureSynthesis(_, assignments) =>
        val m = assignments.translate
        handleSubstitution(m, ctx)
      case SuslikProofStep.SubstL(from, to) =>
        val m = Map(from.translate -> to.translate)
        handleSubstitution(m, ctx)
      case SuslikProofStep.SubstR(from, to) =>
        val m = Map(from.translate -> to.translate)
        handleSubstitution(m, ctx)
      case SuslikProofStep.Close(app, selector, asn, fresh_exist) =>
        // construct an up-to-date inductive clause with synthesis info
        val csapp = app.translate
        val cselector = selector.translate
        val m = fresh_exist.translate
        val clause0 = ctx.predicates(csapp.pred).clauses.find(_.selector == cselector).get
        val clause = CInductiveClause(csapp.pred, clause0.idx, cselector, asn.translate, clause0.existentials.map(_.subst(m)))

        // create deferreds to perform unfolding
        val deferreds = Queue(
          (ctx: ProofContext) => (Proof.UnfoldConstructor(clause.idx) andThen, ctx),
          (ctx: ProofContext) => {
            val csapp1 = ctx.currentAppAlias(csapp)
            val (valueEx, heapEx) = ctx.unfoldedAppExistentials(csapp1)
            (Proof.Exists(valueEx ++ heapEx) andThen, ctx)
          },
          (ctx: ProofContext) => (Proof.Auto, ctx)
        )

        // update context with unfolding info
        val appAliases = ctx.appAliases ++ clause.asn.sigma.apps.map(a => a -> a)
        val unfoldings = ctx.unfoldings + (csapp -> clause)
        val ctx1 = ctx.copy(appAliases = appAliases, unfoldings = unfoldings)

        Result(List(Proof.Noop), List((deferreds, ctx1)))

      /** Terminals */
      case SuslikProofStep.Inconsistency(label) =>
        Result(List(Proof.Inconsistency), Nil)
      case SuslikProofStep.EmpRule(label) =>
        Result(List(Proof.Emp andThen), Nil)

      /** Pure entailments */
      case SuslikProofStep.CheckPost(prePhi, postPhi) =>
        ctx.hints += Hint.PureEntailment(prePhi.conjuncts.map(_.translate), postPhi.conjuncts.map(_.translate))
        Result(List(Proof.Noop), List(withNoDeferreds(ctx)))

      /** Ignored */
      case _ => Result(List(Proof.Noop), List(withNoDeferreds(ctx)))
    }
  }
}
