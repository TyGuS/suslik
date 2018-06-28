package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.language.{Ident, VoidType}
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.logic.unification.{SpatialUnification, UnificationGoal}
import org.tygus.synsl.synthesis._

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

object UnfoldingRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unfolding"

  /*
                      args ⊆ Г
       p(params) = <sel_i(params); clause_i(params)>_i
              b_i = sel_i[args/params]
              c_i = clause_i[args/params]
    ∀i, f_rec; Γ ; { φ ⋀ s_i ; b_i * P } ; { ψ ; Q } ---> S_i
    f_rec : ∀xs, { φ ; p(args) * P } ; { ψ ; Q },
       where xs = (vars { φ ; p(args) * P } ; { ψ ; Q }) U Г
    --------------------------------------------------------------------[Unfold: induction]
        Γ ; { φ ; p(args) * P } ; { ψ ; Q } ---> If(<b_i, S_i>)

   */
  object InductionRule extends SynthesisRule {

    override def toString: Ident = "[Unfold: induction]"

    private def kont(selectors: Seq[PFormula]): StmtProducer = stmts => {
      ruleAssert(selectors.length == stmts.length,
        s"Mismatch in sizes of selectors and sub-programs\n${selectors.length}: $selectors\n${stmts.length}: $stmts")
      ruleAssert(stmts.nonEmpty, s"Induction rule expected one or more subgoals got ${stmts.length}")
      if (stmts.length == 1) stmts.head else {
        val cond_branches = selectors.zip(stmts).reverse
        val ctail = cond_branches.tail
        val finalBranch = cond_branches.head._2
        ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => If(c, tb, eb).simplify }
      }
    }

    /**
      * TODO: Handle multiple predicate application occurrences, i.e., provide multiple sets of sub-goals
      * TODO: This can lead to multiple induction hypotheses, all delivered by the same rule
      */
    private def mkInductiveSubGoals(goal: Goal, env: Environment): Option[(Seq[(PFormula, Goal)], Heaplet)] = {
      val pre = goal.pre
      findHeaplet(_.isInstanceOf[SApp], pre.sigma) match {
        case Some(h@SApp(pred, args, tag)) if tag.contains(0) =>
          // Only 0-tagged (i.e., not yet once unfolded predicates) can be unfolded
          ruleAssert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")

          // Get predicate from the environment
          // TODO: Here's a potential bug, due to variable captures
          // (existnentials in predicate clauses are captured by goal variables)
          // TODO: refresh its existentials!
          val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars)
          val sbst = params.zip(args).toMap
          val remainingChunks = pre.sigma.chunks.filter(_ != h)
          val newGoals = for {
            InductiveClause(_sel, _asn) <- clauses
            sel = _sel.subst(sbst)
            asn = _asn.subst(sbst)
            constraints = asn.phi
            body = asn.sigma
            newPrePhi = mkConjunction(List(sel, pre.phi, constraints))
            _newPreSigma1 = SFormula(body.chunks).bumpUpSAppTags()
            _newPreSigma2 = SFormula(remainingChunks).lockSAppTags()
            newPreSigma = SFormula(_newPreSigma1.chunks ++ _newPreSigma2.chunks)
          } yield (sel, goal.copy(Assertion(newPrePhi, newPreSigma)))
          Some((newGoals, h))
        case _ => None
      }
    }

    private def mkIndHyp(goal: Goal, env: Environment, h: Heaplet): Environment = {
      val fname = Var(goal.fname).refresh(env.functions.keySet.map(Var)).name
      // TODO: provide a proper type, not VOID

      // Re-tagging all predicate occurrences, so the inductive argument
      // would be tagged with Some(1), and everyone else with None(1)
      val SApp(pname, xs, t) = h
      val matcher: Heaplet => Boolean = {
        case SApp(x, ys, q) => x == pname && ys == xs
        case _ => false
      }
      val newPre = goal.pre.bumpUpSAppTags(matcher).lockSAppTags(x => !matcher(x))
      // Bump up twice in the post so that we can't apply IH to its results;
      // TODO: If we want to apply IH more than once to the same heap, we need to produce several copies of the hypothesis with increasing tags
      val newPost = goal.post.lockSAppTags() //bumpUpSAppTags().bumpUpSAppTags() //.lockSAppTags(x => !matcher(x))

      val fspec = FunSpec(fname, VoidType, goal.gamma, newPre, newPost)
      env.copy(functions = env.functions + (fname -> fspec))
    }

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      // TODO: this is a hack to avoid invoking induction where it has no chance to succeed
      if (goal.hasAllocatedBlocks) return Nil

      mkInductiveSubGoals(goal, env) match {
        case None => Nil
        case Some((selGoals, h)) =>
          val newEnv = mkIndHyp(goal, env, h)
          val (selectors, subGoals) = selGoals.unzip
          val goalsWithNewEnv = subGoals.map(g => (g, newEnv))
          List(Subderivation(goalsWithNewEnv, kont(selectors)))
      }
    }
  }

  /*
  Application rule: apply the inductive hypothesis

  TODO: Make sure it works on non-trivial sub-heaps
   */

  object ApplyHypothesisRule extends SynthesisRule {

    override def toString: Ident = "[Unfold: apply-hypothesis]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      (for {
        (_, _f) <- env.functions
        f = _f.refreshExistentials(goal.vars)

        // Find all subsets of the goal's pre that might be unified
        lilHeap = f.pre.sigma
        largHeap = goal.pre.sigma
        largSubHeap <- findLargestMatchingHeap(lilHeap, largHeap)
        callSubPre = goal.pre.copy(sigma = largSubHeap)

        // Try to unify f's precondition and found goal pre's subheaps
        source = UnificationGoal(f.pre, f.params.map(_._2).toSet)
        target = UnificationGoal(callSubPre, goal.gamma.map(_._2).toSet)
        sub <- {
          SpatialUnification.unify(target, source)
        }
        if SMTSolving.valid(goal.pre.phi ==> f.pre.phi.subst(sub))
      } yield {
        val callGoal = mkCallGoal(f, sub, callSubPre, goal)
        val args = f.params.map { case (_, x) => x.subst(sub) }
        val kont: StmtProducer = stmts => {
          ruleAssert(stmts.length == 1, s"Apply-hypotheses rule expected 1 premise and got ${stmts.length}")
          val rest = stmts.head
          SeqComp(Call(None, Var(goal.fname), args), rest)
        }
        Subderivation(List((callGoal, env)), kont)
      }).toSeq
    }

    /**
      * Make a call goal for `f` with a given precondition
      */
    protected[UnfoldingRules] def mkCallGoal(f: FunSpec, sub: Map[Var, Expr], callSubPre: Assertion, goal: Goal): Goal = {
      val preFootprint = callSubPre.sigma.chunks.map(p => goal.deriv.preIndex.indexOf(p)).toSet
      val ruleApp = saveApplication((preFootprint, Set.empty), goal.deriv)
      val callPost = f.post.subst(sub)
      val restPreChunks =
      /*
       If we don't increase tags, bad things might happen.

       For instance, a "list_copy" function starts "tweaking" the pre, so it could apply itself more times,
       eventually flooding the entire universe with copies of the very same list! Since this clearly
       perturbs the laws of existence, we prohibit such an obscenity...

       So, for the reasons of avoid sucking our galaxy into a block hole, we bump up the tags.
       */
        (goal.pre.sigma.chunks.toSet -- callSubPre.sigma.chunks.toSet) ++ callPost.sigma.bumpUpSAppTags().chunks
      val restPre = Assertion(andClean(goal.pre.phi, callPost.phi), SFormula(restPreChunks.toList))
      val callGoal = goal.copy(restPre, newRuleApp = Some(ruleApp))
      callGoal
    }
  }

  /*
   Hypothesis rule with some abduction embedded in it:
   * Relaxes the function by replacing some of the points-to values by ghosts to allow for more unifications
   * Infers the discrepancies and emits new write-goals
   * Uses multiple-sub-derivation mechanism to enable several writes, followed by a call
   */
  object ApplyHypothesisAbduceFrameRule extends SynthesisRule {

    override def toString: Ident = "[Unfold: apply-hypothesis-abduct]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      (for {
        (_, _funSpec) <- env.functions

        // Make a "relaxed" substitution for the spec and for with it
        (f, exSub) = _funSpec.refreshExistentials(goal.vars).relaxFunSpec

        lilHeap = f.pre.sigma
        largHeap = goal.pre.sigma
        matchingHeaps = findLargestMatchingHeap(lilHeap, largHeap)
        // if willNotExplode(matchingHeaps)
        largPreSubHeap <- matchingHeaps
        callSubPre = goal.pre.copy(sigma = largPreSubHeap) // A subheap of the precondition to unify with

        source = UnificationGoal(f.pre, f.params.map(_._2).toSet)
        target = UnificationGoal(callSubPre, goal.gamma.map(_._2).toSet)
        relaxedSub <- SpatialUnification.unify(target, source)
        // Preserve regular variables and fresh existentials back to what they were, if applicable
        actualSub = relaxedSub.filterNot { case (k, v) => exSub.keySet.contains(k) } ++ compose1(exSub, relaxedSub)
        if SMTSolving.valid(goal.pre.phi ==> f.pre.phi.subst(actualSub))
      } yield {
        val callGoal = ApplyHypothesisRule.mkCallGoal(f, actualSub, callSubPre, goal)
        val writeGoals = generateWriteGoals(actualSub, relaxedSub, f, goal)
        val n = writeGoals.length

        val kont: StmtProducer = stmts => {
          ruleAssert(stmts.length == n + 1, s"Apply-hypotheses rule expected ${n + 1} premise and got ${stmts.length}")
          val writes = stmts.take(n)
          val rest = stmts.drop(n).head
          val args = f.params.map { case (_, x) => x.subst(actualSub) }
          // The call goes last
          val k = SeqComp(Call(None, Var(goal.fname), args), rest)
          val writesCallRest = writes.foldRight(k) { case (w, r) => SeqComp(w, r) }
          writesCallRest
        }
        val subGoals = writeGoals.map(wg => (wg, env)) ++ List((callGoal, env))
        Subderivation(subGoals, kont)
      }).toSeq
    }

    private def generateWriteGoals(actualSub: Subst, relaxedSub: Subst, f: FunSpec, goal: Goal): List[Goal] = {
      val ptss = f.pre.sigma.ptss // raw points-to assertions
      for {
        p@PointsTo(x@Var(_), o, e) <- ptss
        if e.subst(relaxedSub) != e.subst(actualSub) // here is a discrepancy
      } yield {
        val wPre = Assertion(pTrue, SFormula(List(PointsTo(x, o, e.subst(relaxedSub)))))
        val wPost = Assertion(pTrue, SFormula(List(PointsTo(x, o, e.subst(actualSub)))))
        val stmt = Store(x, o, e.subst(actualSub))
        val wGoal = goal.copy(pre = wPre, post = wPost)
        wGoal
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
  object CloseRule extends SynthesisRule {

    override def toString: Ident = "[Unfold: close]"

    private val kont: StmtProducer = stmts => {
      ruleAssert(stmts.lengthCompare(1) == 0, s"Close rule expected 1 premise and got ${stmts.length}")
      stmts.head
    }

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val post = goal.post
      val deriv = goal.deriv

      // Does h have a tag that exceeds the maximum allowed unfolding depth?
      def exceedsMaxDepth(h: Heaplet): Boolean = {
        h match {
          case SApp(_,_,Some(t)) => t > env.maxUnfoldingDepth
          case _ => false
        }
      }

      def heapletResults(h: Heaplet): Seq[Subderivation] = h match {
        case SApp(pred, args, Some(t)) =>
          ruleAssert(env.predicates.contains(pred),
            s"Close rule encountered undefined predicate: $pred")
          val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars)

          //ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val substArgs = params.zip(args).toMap
          val subDerivations = for {
            InductiveClause(selector, asn) <- clauses
            // Make sure that existential in the body are fresh
            asnExistentials = asn.vars -- params.toSet
            freshExistentialsSubst = refreshVars(asnExistentials.toList, goal.vars)
            // Make sure that can unfold only once
            actualAssertion = asn.subst(freshExistentialsSubst).subst(substArgs)
            actualConstraints = actualAssertion.phi
            actualBody = actualAssertion.sigma.setUpSAppTags(t + 1, _ => true)
            // If we unfolded too much: back out
            if !actualBody.chunks.exists(h => exceedsMaxDepth(h))
          } yield {
            val actualSelector = selector.subst(freshExistentialsSubst).subst(substArgs)
            val newPhi = simplify(mkConjunction(List(actualSelector, post.phi, actualConstraints)))
            val newPost = Assertion(newPhi, goal.post.sigma ** actualBody - h)

            val postFootprint = Set(deriv.postIndex.indexOf(h))
            val ruleApp = saveApplication((Set.empty, postFootprint), deriv)

            Subderivation(List((goal.copy(post = newPost, newRuleApp = Some(ruleApp)), env)), kont)
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
