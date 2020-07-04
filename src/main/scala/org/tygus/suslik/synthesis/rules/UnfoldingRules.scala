package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{CardType, Ident}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.Termination.Transition
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Unfolding rules deal with predicates and recursion.
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

object UnfoldingRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unfolding"

  object Open extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Open"

    def mkInductiveSubGoals(goal: Goal, h: Heaplet): Option[(Seq[(Expr, Goal)], Heaplet)] = {
      val pre = goal.pre
      val env = goal.env

      h match {
        case SApp(pred, args, PTag(cls, unf), card) if unf < env.config.maxOpenDepth =>
          ruleAssert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")
          val freshSuffix = args.take(1).map(_.pp).mkString("_")
          val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars, freshSuffix)
          // [Cardinality] adjust cardinality of sub-clauses
          val sbst = params.map(_._1).zip(args).toMap + (selfCardVar -> card)
          val remainingSigma = pre.sigma - h
          val newGoals = for {
            c@InductiveClause(_sel, _asn) <- clauses
            sel = _sel.subst(sbst)
            asn = _asn.subst(sbst)
            constraints = asn.phi
            body = asn.sigma
            newPrePhi = pre.phi && constraints && sel
            // The tags in the body should be one more than in the current application:
            _newPreSigma1 = mkSFormula(body.chunks).setSAppTags(PTag(cls, unf + 1))
            newPreSigma = _newPreSigma1 ** remainingSigma
          } yield (sel, goal.spawnChild(Assertion(newPrePhi, newPreSigma), childId = Some(clauses.indexOf(c))))

          // This is important, otherwise the rule is unsound and produces programs reading from ghosts
          // We can make the conditional without additional reading
          // TODO: Generalise this in the future
          val noGhosts = newGoals.forall { case (sel, _) => sel.vars.subsetOf(goal.programVars.toSet) }
          if (noGhosts) Some((newGoals, h)) else None
        case _ => None
      }
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        heaplet <- goal.pre.sigma.chunks
        s <- mkInductiveSubGoals(goal, heaplet) match {
          case None => None
          case Some((selGoals, heaplet)) =>
            val (selectors, subGoals) = selGoals.unzip
            val kont = BranchProducer(selectors) >> HandleGuard(goal) >> ExtractHelper(goal)
            Some(RuleResult(subGoals, kont, this, goal))
        }
      } yield s
    }
  }

  object AbduceCall extends SynthesisRule {

    override def toString: Ident = "AbduceCall"

    def apply(goal: Goal): Seq[RuleResult] = {
      // look at all proper ancestors starting from the root
      // and try to find a companion
      // (If auxiliary abduction is disabled, only look at the root)
      val allCands = goal.companionCandidates.reverse
      val cands = if (goal.env.config.auxAbduction) allCands else allCands.take(1)
      val funLabels = cands.map(a => (a.toFunSpec, Some(a.label))) ++ // companions
        goal.env.functions.values.map(f => (f, None)) // components
      val results = for {
        (_f, l) <- funLabels
        (freshSub, f) = _f.refreshAll(goal.vars)

        // Optimization: do not consider f if its pre has predicates that cannot possibly match ours
        if multiSubset(f.pre.sigma.profile.apps, goal.pre.sigma.profile.apps)

        newGamma = goal.gamma ++ (f.params ++ f.var_decl).toMap // Add f's (fresh) variables to gamma
        call = Call(Var(f.name), f.params.map(_._1), l)
        calleePostSigma = f.post.sigma.setSAppTags(PTag(1, 0))
        callePost = Assertion(f.post.phi, calleePostSigma)
        suspendedCallGoal = Some(SuspendedCallGoal(goal.pre, goal.post, callePost, call, freshSub))
        newGoal = goal.spawnChild(post = f.pre, gamma = newGamma, callGoal = suspendedCallGoal)
      } yield {
        val kont: StmtProducer = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)
        RuleResult(List(newGoal), kont, this, goal)
      }
//      nubBy[RuleResult, SFormula](results, r => r.subgoals.head.post.sigma)
      nubBy[RuleResult, (SProfile, SProfile)](results, r => (r.subgoals.head.post.sigma.profile, r.subgoals.head.callGoal.get.calleePost.sigma.profile))
//      results
    }
  }

  object CallRule extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Call"

    def apply(goal: Goal): Seq[RuleResult] = {
      if (goal.callGoal.isEmpty) return Nil // this goal has no suspended call

      val pre = goal.pre
      val post = goal.post
      val callGoal = goal.callGoal.get.applySubstitution
      val call = callGoal.call
      val budHeap = callGoal.callerPre.sigma - goal.pre.sigma
      val noGhostArgs = call.args.forall(_.vars.subsetOf(goal.programVars.toSet))

      if (post.sigma.isEmp &&                                   // companion's transformed pre-heap is empty
        goal.existentials.isEmpty &&                            // no existentials
        noGhostArgs &&                                          // TODO: if slow, move this check to when substitution is made
        // canEmitCall(budHeap, goal, call.companion) &&           // termination
        SMTSolving.valid(pre.phi ==> post.phi))                 // pre implies post
      {
        // We would like to substitute all the fresh vars in calleePost, but we can't
        // since it might have predicates and their arguments must be variables.
        // So instead we are adding the substitution as the pure precondition
        val calleePostSigma = callGoal.calleePost.sigma.setSAppTags(PTag(budHeap.maxCallTag + 1))
        val newPre = Assertion(pre.phi && callGoal.calleePost.phi, pre.sigma ** calleePostSigma)
        val newPost = callGoal.callerPost
        val newGoal = goal.spawnChild(pre = newPre, post = newPost, callGoal = None)
        val postCallTransition = Transition(goal, newGoal)
        val kont: StmtProducer = PrependProducer(call) >> HandleGuard(goal) >> ExtractHelper(goal)
        List(RuleResult(List(newGoal), kont, this,
          List(postCallTransition) ++ companionTransition(callGoal, goal)))
      }
      else Nil
    }

    def companionTransition(callGoal: SuspendedCallGoal, goal: Goal): Option[Transition] = callGoal.call.companion match {
      case None => None // Non-recursive call does not correspond to transition in the trace
      case Some(label) => {
        val companion = goal.ancestorWithLabel(label).get
        val cardVars = companion.pre.vars.filter(_.getType(companion.gamma).contains(CardType)).toList
        val sub = compose(callGoal.companionToFresh, callGoal.freshToActual)
        val nonProgressingFlipped = cardVars.zip(cardVars.map(_.subst(sub))).filter(_._2.isInstanceOf[Var])
        val nonProgressing = nonProgressingFlipped.map{ case (v, e) => (e.asInstanceOf[Var], v) }
        Some(Transition(goal.label, label, List(), nonProgressing))
      }
    }

    // [Cardinality] Checking size constraints before emitting the call
    def canEmitCall(budHeap: SFormula, goal: Goal, l: Option[GoalLabel]): Boolean = l match {
      case None => true // non-recursive call
      case Some(label) => {
        val companion = goal.ancestorWithLabel(label).get
        val companionHeap = companion.pre.sigma
        goal.env.config.termination match {
          case `totalSize` => totalLT(budHeap, companionHeap, goal.pre.phi)
          case `lexicographic` => lexiLT(budHeap, companionHeap, goal.pre.phi)
        }
      }
    }
  }



  /*
  Close rule: unroll a predicate in the post-state

              p(params) := { true ? b }
    Γ ; { φ ; P } ; { ψ ; b[args/params] * Q } ---> S
    ---------------------------------------------------- [close]
        Γ ; { φ ; P } ; { ψ ; p(args) * Q } ---> S

   */
  object Close extends SynthesisRule {

    override def toString: Ident = "Close"

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post
      val env = goal.env

      def heapletResults(h: Heaplet): Seq[RuleResult] = h match {
        case SApp(pred, args, PTag(cls, unf), card) =>
          if (unf >= env.config.maxCloseDepth) return Nil

          ruleAssert(env.predicates.contains(pred),
            s"Close rule encountered undefined predicate: $pred")
          val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars)

          //ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val paramNames = params.map(_._1)

          // [Cardinality] adjust cardinality of sub-clauses
          val substArgs = paramNames.zip(args).toMap + (selfCardVar -> card)

          val subDerivations = for {
            InductiveClause(selector, asn) <- clauses
            // Make sure that existential in the body are fresh
            asnExistentials = asn.vars -- paramNames.toSet -- Set(selfCardVar)
            freshSuffix = args.take(1).map(_.pp).mkString("_")
            freshExistentialsSubst = refreshVars(asnExistentials.toList, goal.vars, freshSuffix)
            // Make sure that can unfold only once
            actualAssertion = asn.subst(freshExistentialsSubst).subst(substArgs)
            actualConstraints = actualAssertion.phi
            actualBody = actualAssertion.sigma.setSAppTags(PTag(cls, unf + 1))
            // If we unfolded too much: back out
            //             if !actualBody.chunks.exists(h => exceedsMaxDepth(h))
          } yield {
            val actualSelector = selector.subst(freshExistentialsSubst).subst(substArgs)
            val newPhi = post.phi && actualConstraints && actualSelector
            val newPost = Assertion(newPhi, goal.post.sigma ** actualBody - h)

            val kont = IdProducer >> HandleGuard(goal) >> ExtractHelper(goal)

            RuleResult(List(goal.spawnChild(post = newPost)), kont, this, goal)
          }
          subDerivations
        case _ => Nil
      }

      for {
        h <- goal.post.sigma.chunks
        s <- heapletResults(h)
      } yield s
    }
  }
}
