package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.{Hint, Proof}
import org.tygus.suslik.certification.targets.htt.logic.Sentences._
import org.tygus.suslik.certification.targets.htt.program.Statements._

object ProofTranslation {
  def irToProofSteps(node: IR.Node) : Proof.Step = {
    def elimExistentials(ex: Seq[CExpr], nested: Boolean = false): Proof.Step = {
      if (ex.nonEmpty) {
        if (nested) Proof.MoveToCtxDestructFoldLeft(ex) else Proof.ElimExistential(ex)
      } else Proof.Noop
    }

    def initPre(asn: CAssertion, uniqueName: String): Proof.Step = {
      val phi = asn.phi
      val sigma = asn.sigma

      // move pure part to context
      val pureToCtx = if (!phi.isTrivial) {
        val hyps = if (phi.conjuncts.isEmpty) Seq(CVar(s"phi_$uniqueName")) else phi.conjuncts.indices.map(i => CVar(s"phi_$uniqueName$i"))
        Proof.MoveToCtxDestruct(hyps)
      } else Proof.Noop

      // move spatial part to context, and then substitute where appropriate
      val spatialToCtx = Proof.MoveToCtxDestruct(Seq(CVar(s"sigma_$uniqueName"))) >> Proof.Sbst

      // move predicate apps to context, if any
      val sappToCtx = if (sigma.apps.nonEmpty) {
        val appNames = sigma.apps.map(app => CVar(app.hypName))
        Proof.MoveToCtxDestructFoldRight(appNames)
      } else Proof.Noop

      pureToCtx >> spatialToCtx >> sappToCtx
    }

    def solvePost(asn: CAssertion, ex: Seq[CExpr], unfoldings: IR.Unfoldings): Proof.Step = {
      val valueExElim = Proof.Exists(ex)

      /**
        * Existentials for the current assertion need to be provided eagerly, so look ahead to find out
        * the maximally unfolded, "flattened" form of the heap
        *
        * @param app the predicate app to flatten
        * @return the points-to's and pred apps in the unfolded heap; any pred apps that remain have already been
        *         established as facts earlier on, so there is no need to unfold further
        */
      def toUnfoldedHeap(app: CSApp): (Seq[CPointsTo], Seq[CSApp]) = unfoldings.get(app) match {
        case Some(a) =>
          val sigma = a.asn.sigma
          val (ptss, apps) = sigma.apps.map(toUnfoldedHeap).unzip
          (sigma.ptss ++ ptss.flatten, apps.flatten)
        case None =>
          (Seq.empty, Seq(app))
      }

      // Eliminate heap existentials (one for each predicate application in the assertion)
      val apps = asn.sigma.apps
      val heapExElim = for (app <- apps) yield {
        val (unfoldedPtss, unfoldedApps) = toUnfoldedHeap(app)
        Proof.Exists(Seq(CSFormula("", unfoldedApps, unfoldedPtss)))
      }

      // For each predicate application, unfold the correct constructor and recursively solve its expanded form
      val rest = for {
        app <- apps
        // If `app` isn't found in the unfoldings, its truth was already established earlier on
        c <- unfoldings.get(app)
      } yield Proof.UnfoldConstructor(c.idx) >>> solvePost(c.asn, c.existentials, unfoldings)

      val p = valueExElim >>> heapExElim.foldLeft[Proof.Step](Proof.Noop)(_ >>> _) >>> Proof.Auto >> rest.foldLeft[Proof.Step](Proof.Noop)(_ >> _)
      p
    }

    var currCallId = 0
    def freshCallId: String = { currCallId += 1; s"call$currCallId" }

    def visit(node: IR.Node): Proof.Step = node match {
      case IR.Init(ctx, next) =>
        val goal = ctx.topLevelGoal.get.subst(ctx.substVar)
        Proof.StartProof(goal.programVars) >>
          // Pull out any precondition ghosts and move precondition heap to the context
          Proof.GhostElimPre >>
          Proof.MoveToCtxDestructFoldLeft(goal.universalGhosts) >>
          Proof.ElimExistential(goal.pre.heapVars) >>
          initPre(goal.pre, "self") >>
          // store heap validity assertions
          Proof.GhostElimPost >>
          visit(next.head)
      case IR.EmpRule(ctx) =>
        val topLevelGoal = ctx.topLevelGoal.get
        val post = topLevelGoal.post.subst(ctx.subst).subst(ctx.substVar)
        val existentials = topLevelGoal.existentials.map(_.substVar(ctx.substVar).subst(ctx.subst).subst(ctx.substVar))
        val unfoldings = ctx.unfoldings.map { case (app, e) => app.subst(ctx.substVar).subst(ctx.subst) -> e.subst(ctx.substVar).subst(ctx.subst) }
        Proof.Emp >>> solvePost(post, existentials, unfoldings)
      case IR.AbduceCall(new_vars, f_pre, calleePost, call, freshSub, freshToActual, next, ctx) =>
        visit(next.head)
      case IR.Call(CCall(_, args), next, ctx) =>
        val callId = freshCallId
        val nestedContext = ctx.nestedContext.get
        val f = ctx.nestedContext.get.funspec.subst(ctx.substVar).subst(nestedContext.freshToActual).subst(ctx.substVar)
        // Move the part of the heap relevant to the call abduction to the beginning
        Proof.CallPre(f.pre.sigma) >>
          // Provide the necessary existentials so that the precondition of the call goal is met,
          // and then execute the call
          Proof.Call(args, f.ghostParamVars.filterNot(_.isCard)) >>
          solvePost(f.pre, Seq.empty, Map.empty) >>
          Proof.MoveToCtx(Seq(CVar(s"h_$callId"))) >>
          // The postcondition of the call abduction becomes the precondition of the companion
          elimExistentials(f.existentials) >>
          elimExistentials(f.post.subst(ctx.subst).heapVars) >>
          initPre(f.post, callId) >>
          // Store validity hypotheses in context
          Proof.StoreValid >>
          visit(next.head)
      case IR.Free(CFree(v, sz), next, _) =>
        (0 until sz).map(o => Proof.Dealloc(v, o)).reduceLeft[Proof.Step](_ >> _) >> visit(next.head)
      case IR.Read(CLoad(to, _, from, offset), next, ctx) =>
        Proof.Read(to.substVar(ctx.substVar), from.substVar(ctx.substVar), offset) >> visit(next.head)
      case IR.Write(CStore(to, offset, e), next, ctx) =>
        val step = Proof.Write(to.substVar(ctx.substVar), offset, e)
        // SSL's `Write` rule does an implicit frame under normal circumstances, but not during a call synthesis
        val step1 = if (ctx.nestedContext.isDefined) step else step >> Proof.WritePost(to, offset)
        step1 >> visit(next.head)
      case IR.Malloc(CMalloc(to, tpe, sz), next, ctx) =>
        Proof.Alloc(to.substVar(ctx.substVar), tpe, sz) >> visit(next.head)
      case IR.PureSynthesis(_, next, _) =>
        visit(next.head)
      case IR.Close(_, _, _, _, next, _) =>
        visit(next.head)
      case IR.Branch(cond, next, ctx) =>
        Proof.Branch(cond.subst(ctx.substVar)) >> Proof.SubProof(next.map(visit))
      case IR.Open(app, clauses, selectors, next, ctx) =>
        val branchSteps = next.zip(clauses).map { case (n, c) =>
          val c1 = c.subst(n.ctx.substVar)
          val res = visit(n)
          if (res == Proof.Error) {
            Proof.OpenPost(app.subst(ctx.substVar))  // Don't emit branch prelude if inconsistent
          } else {
            Proof.OpenPost(app.subst(ctx.substVar)) >>
            elimExistentials(c1.existentials) >>
            elimExistentials(c1.asn.heapVars) >>
            initPre(c1.asn, app.uniqueName) >>
            res
          }
        }
        Proof.Open(selectors.map(_.subst(ctx.substVar))) >> Proof.SubProof(branchSteps)
      case IR.Inconsistency(_) => Proof.Error
      case IR.CheckPost(prePhi, postPhi, next, _) => visit(next.head)
    }

    pruneUnusedReads(visit(node).simplify) >> Proof.EndProof
  }

  def irToHints(node: IR.Node) : Seq[Hint] = {
    def visit(node: IR.Node, hints: Seq[Hint]) : Seq[Hint] = node match {
      case IR.Init(ctx, next) =>
        visit(next.head, ctx.predicateEnv.values.map(p => Hint.PredicateSetTransitive(p)).toSeq)
      case IR.CheckPost(prePhi, postPhi, next, _) =>
        visit(next.head, hints :+ Hint.PureEntailment(prePhi, postPhi))
      case _:IR.Inconsistency | _:IR.EmpRule =>
        hints
      case _:IR.Open | _:IR.Branch =>
        node.next.foldLeft(hints){ case (hints, next) => visit(next, hints) }
      case _ =>
        visit(node.next.head, hints)
    }

    visit(node, Seq.empty).filter(_.numHypotheses > 0)
  }

  def pruneUnusedReads(step: Proof.Step): Proof.Step = {
    def visit(step: Proof.Step): (Proof.Step, Set[CVar]) = step match {
      case Proof.SeqComp(s1, s2) =>
        val (s2New, s2Used) = visit(s2)
        val (s1New, s1Used) = visit(s1)
        s1 match {
          case Proof.Read(to, _, _) if !s2Used.contains(to) => (s2New, s2Used)
          case _ => (s1New >> s2New, s1Used ++ s2Used)
        }
      case Proof.SeqCompAlt(s1, s2) =>
        val (s2New, s2Used) = visit(s2)
        val (s1New, s1Used) = visit(s1)
        s1 match {
          case Proof.Read(to, _, _) if !s2Used.contains(to) => (s2New, s2Used)
          case _ => (s1New >>> s2New, s1Used ++ s2Used)
        }
      case Proof.SubProof(branches) =>
        val (branchesNew, branchesUsed) = branches.map(visit).unzip
        (Proof.SubProof(branchesNew), branchesUsed.reduce(_ ++ _))
      case Proof.Read(to, from, offset) => (step, Set(to, from))
      case Proof.Write(to, offset, e) => (step, Set(to) ++ e.vars.toSet)
      case Proof.WritePost(to, offset) => (step, Set(to))
      case Proof.Alloc(to, tpe, sz) => (step, Set(to))
      case Proof.Dealloc(v, offset) => (step, Set(v))
      case Proof.Call(args, _) => (step, args.flatMap(_.vars).toSet)
      case Proof.Open(selectors) => (step, selectors.flatMap(_.vars).toSet)
      case Proof.Branch(cond) => (step, cond.vars.toSet)
      case _ => (step, Set.empty)
    }
    visit(step)._1
  }
}
