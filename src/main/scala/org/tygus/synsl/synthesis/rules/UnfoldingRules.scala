package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.language.{Ident, VoidType}
import org.tygus.synsl.logic._
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
      val conds = selectors.map(_.toExpr)
      ruleAssert(selectors.length == stmts.length,
        s"Mismatch in sizes of selectors and sub-programs\n${selectors.length}: $selectors\n${stmts.length}: $stmts")
      ruleAssert(stmts.nonEmpty, s"Induction rule expected one or more subgoals got ${stmts.length}")
      if (stmts.length == 1) stmts.head else {
        val cond_branches = conds.zip(stmts).reverse
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
      val newPost = goal.post.bumpUpSAppTags().bumpUpSAppTags() //.lockSAppTags(x => !matcher(x))

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

    /**
      * TODO: Handle multiple predicate application occurrences, i.e., provide multiple sets of sub-goals
      * TODO: This can lead to multiple induction hypotheses, all delivered by the same rule
      */
    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      (for {
        (_, f) <- env.functions

        // Find all subsets of the goal's pre that might be unified
        lilHeap = f.pre.sigma
        largHeap = goal.pre.sigma
        largSubHeap <- findLargestMatchingHeap(lilHeap, largHeap)
        targetPre = goal.pre.copy(sigma = largSubHeap)

        // Try to unify f's precondition and found goal pre's subheaps
        source = UnificationGoal(f.pre, f.params.map(_._2).toSet)
        target = UnificationGoal(targetPre, goal.gamma.map(_._2).toSet)
        sigma <- {
          SpatialUnification.unify(target, source)
        }
      } yield {
        // Make sure that existential in the post are fresh
        val fExistentials = (f.post.vars -- f.pre.vars) -- f.params.map(_._2).toSet
        val freshExistentialsSubst = refreshVars(fExistentials.toList, goal.vars)
        // Make sure that can unfold only once
        val actualPost = f.post.subst(freshExistentialsSubst).subst(sigma)


        val newPreChunks =
          (goal.pre.sigma.chunks.toSet -- targetPre.sigma.chunks.toSet) ++ actualPost.subst(sigma).sigma.chunks
        val newPre = Assertion(PAnd(goal.pre.phi, actualPost.phi), SFormula(newPreChunks.toList))

        val deriv = goal.deriv
        val preFootprint = targetPre.sigma.chunks.map(p => deriv.preIndex.indexOf(p)).toSet
        val ruleApp = saveApplication((preFootprint, Set.empty), deriv)

        val newGoal = goal.copy(newPre, newRuleApp = Some(ruleApp))
        val args = f.params.map { case (_, x) => x.subst(sigma) }
        val kont: StmtProducer = stmts => {
          ruleAssert(stmts.length == 1, s"Apply-hypotheses rule expected 1 premise and got ${stmts.length}")
          val rest = stmts.head
          SeqComp(Call(None, Var(goal.fname), args), rest)
        }
        Subderivation(List((newGoal, env)), kont)
      }).toSeq
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
      // TODO: super-mega-dirty hack!
      // Avoiding exponential blow-up by looking at the number of allowed environments left
      val leftUnfoldings = env.unfoldingsLeft
      //if (leftUnfoldings <= 0) return Nil

      findHeaplet({
        case SApp(pred, args, Some(t)) => t <= leftUnfoldings
        case _ => false
      }, goal.post.sigma) match {
        case None => Nil
        case Some(h@SApp(pred, args, Some(t))) =>
          ruleAssert(env.predicates.contains(pred) && t <= leftUnfoldings,
            s"Close rule encountered undefined predicate: $pred")
          // TODO: Here's a potential bug, due to variable captures
          // (existnentials in predicate clauses are captured by goal variables)
          // TODO: refresh its existentials!
          val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars)

          //ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val substArgs = params.zip(args).toMap
          val subDerivations = for (InductiveClause(selector, asn) <- clauses) yield {

            // Make sure that existential in the body are fresh
            val asnExistentials = asn.vars -- params.toSet
            val freshExistentialsSubst = refreshVars(asnExistentials.toList, goal.vars)
            // Make sure that can unfold only once
            val actualAssertion = asn.subst(freshExistentialsSubst).subst(substArgs)
            val actualConstraints = actualAssertion.phi
            val actualBody = actualAssertion.sigma.setUpSAppTags(t + 1, _ => true)

            val actualSelector = selector.subst(freshExistentialsSubst).subst(substArgs)
            val newPhi = simplify(mkConjunction(List(actualSelector, post.phi, actualConstraints)))
            val newPost = Assertion(newPhi, goal.post.sigma ** actualBody - h)

            val postFootprint = Set(deriv.postIndex.indexOf(h))
            val ruleApp = saveApplication((Set.empty, postFootprint), deriv)

            Subderivation(List((goal.copy(post = newPost, newRuleApp = Some(ruleApp)), env.copy(unfoldingsLeft = leftUnfoldings - 1))), kont)
          }
          subDerivations
        case Some(h) =>
          ruleAssert(false, s"Close rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }

}
