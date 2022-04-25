package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.language.Expressions.{CExpr, CSApp, CVar}
import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences.CAssertion
import org.tygus.suslik.certification.targets.htt.translation.ProofContext.AppliedConstructor
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Evaluator.{Deferred, EvaluatorException}
import org.tygus.suslik.certification.traversal.Interpreter
import org.tygus.suslik.certification.traversal.Interpreter.Result
import org.tygus.suslik.language.Expressions.{Unknown, Var}
import org.tygus.suslik.language.Statements.{Free, Load, Malloc, Store}
import org.tygus.suslik.logic.SApp

import scala.collection.immutable.ListMap

object ProofInterpreter extends Interpreter[SuslikProofStep, Proof.Step, ProofContext] {
  private def withNoDeferred(ctx: ProofContext): (List[Proof.Step], Option[Deferred[Proof.Step, ProofContext]], ProofContext) = (Nil, None, ctx)

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

  def handleSubstitution(m: Map[CVar, CExpr], ctx: ProofContext): Interpreter.Result[Proof.Step, ProofContext] = {
    val affectedApps = ctx.appsAffectedBySubst(m)
    val ctx1 = ctx.withSubst(m, affectedApps)
    val steps = renameAppsStep(affectedApps)
    Result(steps, List(withNoDeferred(ctx1)))
  }

  def handleShelving(app: CSApp, newApps: Seq[CSApp], ctx: ProofContext): (List[Proof.Step], List[Proof.Step]) = {
    ctx.appsToSolve.indexOf(app) match {
      case -1 => throw EvaluatorException(s"${app.pp} not found in list of predicate applications to solve")
      case 0 => (Nil, Nil)
      case idx =>
        val remainingGoals = ctx.appsToSolve.length - idx - 1 + newApps.length + ctx.numSubgoals
        val preSteps = List.tabulate(idx)(_ => Proof.Shelve)
        val postSteps = List.tabulate(remainingGoals)(_ => Proof.Shelve) ++ (if (idx + remainingGoals == 0) Nil else List(Proof.Unshelve))
        (preSteps, postSteps)
    }
  }

  override def interpret(value: SuslikProofStep, ctx: ProofContext): Interpreter.Result[Proof.Step, ProofContext] = {
    implicit val env = ctx.env
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
        val deferred = (ctx: ProofContext) => {
          val ex = ctx.postEx.toSeq.map {
            // if proof ended without instantiating this existential, provide default witness
            case (start, (typ, end)) if start == end => typ.defaultExpr
            // otherwise, provide final substituted expression
            case (_, (_, end)) => end
          }
          val valueEx = Proof.Exists(ex) andThen

          val heapEx = sapps.map(app => {
            val app1 = ctx.currentAppAlias(app)
            val heap = ctx.unfoldedApp(app1)
            Proof.Exists(List(heap)) andThen
          }).toList

          val steps = valueEx :: heapEx ++ List(Proof.Auto)
          val appsToSolve = cgoal.post.sigma.apps.map(ctx.currentAppAlias)
          val ctx1 = ctx.copy(appsToSolve = appsToSolve)

          (steps, ctx1)
        }

        // initialize context with post-condition info and predicate hints, if any
        val appAliases = (cgoal.pre.sigma.apps ++ cgoal.post.sigma.apps).map(a => a -> a).toMap
        if (env.config.certSetRepr) {
          val hammer = env.config.certHammerPure
          ctx.hints ++= ctx.predicates.values.map(p => Hint.PredicateSetCongruence(p, hammer))
        }
        val postEx = ListMap(cgoal.existentials.map(v => v -> (goal.getType(Var(v.name)).translate, v)): _*)
        val ctx1 = ctx.copy(postEx = postEx, appAliases = appAliases)

        Result(steps, List((Nil, Some(deferred), ctx1)))
      case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) =>
        val pre = f.pre.translate
        val post = f.post.translate
        val programVars = f.params.map(_._1.translate)
        val universalGhosts = pre.valueVars.diff(programVars)
        val goal = Proof.Goal(pre, post, gamma.translate, programVars, universalGhosts, f.name)
        val ctx1 = ctx.copy(callGoal = Some(goal))
        Result(List(), List(withNoDeferred(ctx1)))

      /** Control flow */
      case SuslikProofStep.Branch(cond) =>
        val childContexts = List(ctx.copy(numSubgoals = ctx.numSubgoals + 1), ctx)
        Result(List(Proof.Branch(cond.translate)), childContexts.map(withNoDeferred))
      case SuslikProofStep.Open(sapp, freshExistentials, freshParamArgs, selectors) =>
        val exSub = freshExistentials.translate
        val argSub = freshParamArgs.translate
        val pred = ctx.predicates(sapp.pred)
        val clauses = pred.clauses.toList.map { clause =>
          val existentials = clause.existentials.map(_.substVar(exSub))
          val asn = clause.asn.subst(exSub).subst(argSub)
          (clause.idx, existentials, asn)
        }
        val csapp = sapp.translate
        val cselectors = selectors.map(_.translate)
        val branchSteps = clauses.map { case (_, existentials, asn) =>
          List(
            Proof.ElimExistential(existentials),
            Proof.ElimExistential(asn.heapVars)
          ) ++ initPre(asn, csapp.uniqueName)
        }
        val steps = List(Proof.Open(cselectors, csapp))

        val numClauses = pred.clauses.length
        val childCtxs = clauses.map { case (idx, _, asn) =>
          val newApps = asn.sigma.apps.map(a => a -> a).toMap
          val numSubgoals = numClauses - idx + ctx.numSubgoals
          ctx.copy(appAliases = ctx.appAliases ++ newApps, numSubgoals = numSubgoals)
        }
        Result(steps, branchSteps.zip(childCtxs).map { case (s, c) => (s, None, c) })

      /** Program statements */
      case SuslikProofStep.Read(ghostFrom, ghostTo, Load(to, _, from, offset)) =>
        val readStep = Proof.Read(to.translate, from.translate, offset)
        val renameStep = Proof.Rename(ghostFrom.name, ghostTo.name)
        val m = Map(ghostFrom.translate -> ghostTo.translate)
        val affectedApps = ctx.appsAffectedBySubst(m)
        val ctx1 = ctx.withSubst(m, affectedApps)
        val steps = readStep :: renameStep :: renameAppsStep(affectedApps)
        Result(steps, List(withNoDeferred(ctx1)))
      case SuslikProofStep.Write(Store(to, offset, e)) =>
        val writeStep = Proof.Write(to.translate, offset, e.translate)
        val writePostStep = Proof.WritePost(to.translate, offset)
        val steps = if (ctx.callGoal.isDefined) List(writeStep) else List(writeStep, writePostStep)
        Result(steps, List(withNoDeferred(ctx)))
      case SuslikProofStep.Malloc(ghostFrom, ghostTo, Malloc(to, tpe, sz)) =>
        val allocStep = Proof.Alloc(to.translate, tpe.translate, sz)
        val renameStep = Proof.Rename(ghostFrom.name, ghostTo.name)
        val m = Map(ghostFrom.translate -> ghostTo.translate)
        val affectedApps = ctx.appsAffectedBySubst(m)
        val ctx1 = ctx.withSubst(m, affectedApps)
        val steps = allocStep :: renameStep :: renameAppsStep(affectedApps)
        Result(steps, List(withNoDeferred(ctx1)))
      case SuslikProofStep.Free(Free(v), size) =>
        val steps = (0 until size).map(i => Proof.Dealloc(v.translate, i)).toList
        Result(steps, List(withNoDeferred(ctx)))
      case SuslikProofStep.Call(freshToActual, _) =>
        val callId = ctx.nextCallId
        val callGoal = ctx.callGoal.get
        val sub = freshToActual.translate
        val pre = callGoal.pre.subst(sub)
        val post = callGoal.post.subst(sub)
        val universalGhosts = callGoal.universalGhosts.filterNot(_.isCard).map(_.subst(sub))
        val existentials = callGoal.existentials.filterNot(_.isCard).map(_.substVar(sub))
        val preApps = pre.sigma.apps.map(ctx.currentAppAlias)

        val steps = List(
          // Move the part of the heap relevant to the call abduction to the beginning
          Proof.CallPre(pre.sigma),
          // Provide the necessary existentials so that the precondition of the call goal is met,
          // and then execute the call
          Proof.Call(universalGhosts),
          Proof.Exists(preApps.map(ctx.unfoldedApp)) andThen,
          Proof.Auto
        )

        val childSteps = List(
          Proof.MoveToCtx(List(CVar(s"h_call$callId"))),
          // The postcondition of the call abduction becomes the precondition of the companion
          Proof.ElimExistential(existentials),
          Proof.ElimExistential(post.heapVars)
        ) ++ initPre(post, s"call$callId") ++ List(Proof.StoreValid)

        val newApps = post.sigma.apps.map(a => a -> a).toMap
        val ctx1 = ctx.copy(appsToSolve = preApps, callGoal = None, nextCallId = callId + 1, appAliases = ctx.appAliases ++ newApps)

        Result(steps, List((childSteps, None, ctx1)))

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
      case SuslikProofStep.HeapUnifyUnfold(preApp, postApp, m) =>
        val cpreApp = preApp.translate
        val cpostApp = postApp.translate
        val ctx1 = ctx.withUnify(cpreApp, cpostApp, m.translate)
        val steps = renameAppsStep(Map(cpostApp -> cpreApp))
        Result(steps, List((Nil, None, ctx1)))
      case SuslikProofStep.FrameUnfold(_, h_post) =>
        h_post match {
          case app:SApp =>
            val csapp = app.translate
            val deferred = (ctx: ProofContext)=> {
              val csapp1 = ctx.currentAppAlias(csapp)
              val newApps = ctx.newAppsAfterUnfolding(csapp1)
              val (preSteps, postSteps) = handleShelving(csapp1, newApps, ctx)
              val ctx1 = ctx.solveApp(csapp1, newApps)

              (preSteps ++ List(Proof.FrameUnfold) ++ postSteps, ctx1)
            }
            Result(List(), List((Nil, Some(deferred), ctx)))
          case _ => Result(List(), List(withNoDeferred(ctx)))
        }
      case SuslikProofStep.Close(app, selector, asn, fresh_exist) =>
        // build an instance of an invoked inductive clause with synthesis info
        val csapp = app.translate
        val cselector = selector.translate
        val m = fresh_exist.translate
        val clause = ctx.predicates(csapp.pred).clauses.find(_.selector == cselector).get
        val constructor = AppliedConstructor(clause.idx, clause.existentials.map(_.subst(m)), asn.translate)

        // create deferred to perform unfolding
        val deferred = (ctx: ProofContext) => {
          val csapp1 = ctx.currentAppAlias(csapp)
          val (valueEx, heapEx) = ctx.existentialsAfterUnfolding(csapp1)

          val newApps = ctx.newAppsAfterUnfolding(csapp1)
          val (preSteps, postSteps) = handleShelving(csapp1, newApps, ctx)
          val ctx1 = ctx.solveApp(csapp1, newApps)

          val steps = List(
            Proof.Close(constructor.idx) andThen,
            Proof.Exists(valueEx ++ heapEx) andThen,
            Proof.Auto
          )

          (preSteps ++ steps ++ postSteps, ctx1)
        }

        // update context with unfolding info
        val appAliases = ctx.appAliases ++ constructor.asn.sigma.apps.map(a => a -> a)
        val unfoldings = ctx.unfoldings + (csapp -> constructor)
        val ctx1 = ctx.copy(appAliases = appAliases, unfoldings = unfoldings)

        Result(List(), List((Nil, Some(deferred), ctx1)))

      /** Terminals */
      case SuslikProofStep.Inconsistency(label) =>
        Result(List(Proof.Inconsistency), Nil)
      case SuslikProofStep.EmpRule(label) =>
        Result(List(Proof.Emp andThen), Nil)

      /** Pure entailments */
      case SuslikProofStep.CheckPost(prePhi, postPhi, gamma) =>
        val hammer = env.config.certHammerPure
        val preConjuncts = prePhi.conjuncts.filterNot(_.isInstanceOf[Unknown]).map(_.translate)
        val postConjuncts = postPhi.conjuncts.filterNot(_.isInstanceOf[Unknown]).map(_.translate)
        ctx.hints += Hint.PureEntailment(preConjuncts, postConjuncts, gamma.translate, hammer)
        Result(List(), List(withNoDeferred(ctx)))

      /** Ignored */
      case _ => Result(List(), List(withNoDeferred(ctx)))
    }
  }
}
