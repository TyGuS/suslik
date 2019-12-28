package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.{Ident, VoidType}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.unification.{SpatialUnification, UnificationGoal}
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.LogicalRules.mkSFormula
import org.tygus.suslik.synthesis.rules.Rules.{extractHelper, _}

/**
  * Unfolding rules deal with predicates and recursion.
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

object UnfoldingRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unfolding"

  object Open extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Open"

    override def cost: Int = 1

    def mkInductiveSubGoals(goal: Goal, h: Heaplet): Option[(Seq[(Expr, Goal)], Heaplet)] = {
      val pre = goal.pre
      val env = goal.env

      h match {
        case SApp(pred, args, Some(t)) if t < env.config.maxOpenDepth =>
          ruleAssert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")
          val freshSuffix = args.take(1).map(_.pp).mkString("_")
          val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars, freshSuffix)
          val sbst = params.map(_._2).zip(args).toMap
          val remainingSigma = pre.sigma - h
          val newGoals = for {
            c@InductiveClause(_sel, _asn) <- clauses
            sel = _sel.subst(sbst)
            asn = _asn.subst(sbst)
            constraints = asn.phi
            body = asn.sigma
            newPrePhi = pre.phi && constraints && sel
            // The tags in the body should be one more than in the current application:
            _newPreSigma1 = mkSFormula(body.chunks).setUpSAppTags(t + 1)
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
            val kont = branchProducer(selectors) >> handleGuard(goal) >> extractHelper(goal)
            Some(RuleResult(subGoals, kont, Footprint(singletonHeap(heaplet), emp), this))
        }
      } yield s
    }
  }

 
  /*
  Application rule: apply the inductive hypothesis

  TODO: Make sure it works on non-trivial sub-heaps
   */

  object CallRule extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Call"

    override def cost: Int = 1

    def apply(goal: Goal): Seq[RuleResult] = {
      // look at all proper ancestors starting from the root
      // and try to find a companion
      // (If auxiliary abduction is disabled, only look at the root)
      val allCands = goal.companionCandidates.reverse
      val cands = if (goal.env.config.auxAbduction) allCands else allCands.take(1)
      val funLabels = cands.map(a => (a.toFunSpec, Some(a.label))) ++ // companions
        goal.env.functions.values.map (f => (f, None)) // components
      for {
        (f, l) <- funLabels

        // Find all subsets of the goal's pre that might be unified
        lilHeap = f.pre.sigma
        largHeap = goal.pre.sigma
        largSubHeap <- findLargestMatchingHeap(lilHeap, largHeap)
        callSubPre = goal.pre.copy(sigma = largSubHeap)

        // Try to unify f's precondition and found goal pre's subheaps
        source = UnificationGoal(f.pre, f.params.map(_._2).toSet)
        target = UnificationGoal(callSubPre, goal.programVars.toSet)
        sub <- SpatialUnification.unify(target, source).toList
        if respectsOrdering(largSubHeap, lilHeap.subst(sub))
        args = f.params.map { case (_, x) => x.subst(sub) }
        if args.flatMap(_.vars).toSet.subsetOf(goal.vars)
        if SMTSolving.valid(goal.pre.phi ==> f.pre.phi.subst(sub))
        // Check that the goal's subheap had at least one unfolding
        callGoal <- mkCallGoal(f, sub, callSubPre, goal)
      } yield {
        val kont: StmtProducer = prepend(Call(None, Var(f.name), args, l)) >> handleGuard(goal) >> extractHelper(goal)
        RuleResult(List(callGoal), kont, Footprint(largSubHeap, emp), this)
      }
    }

    /**
      * Make a call goal for `f` with a given precondition
      */
    def mkCallGoal(f: FunSpec, sub: Map[Var, Expr], callSubPre: Assertion, goal: Goal): List[Goal] = {
//      val freshSuffix = sub.values.map(_.pp).mkString("_")
      val freshSuffix = f.params.map(_._2.subst(sub).pp).mkString("_")
      val callPost = f.refreshExistentials(goal.vars, freshSuffix).post.subst(sub)
      val newEnv = if (f.name == goal.fname) goal.env else {
        // To avoid more than one application of a library function
        val funs = goal.env.functions.filterKeys(_ != f.name)
        goal.env.copy(functions = funs)
      }
//      val addedChunks1 = callPost.sigma.bumpUpSAppTags()
      val addedChunks2 = callPost.sigma.lockSAppTags()
      // Here we return two options for added chunks:
      // (a) with bumped tags
      // (b) with locked tags
      // The former enables applications of other functions (tree-flatten)
      // The latter enables application of the same recursive function (tree-flatten-acc),
      // but "focused" on a different some(1)-tagged predicate applications. Both are sound.
      for {
//        acs <- List(addedChunks1, addedChunks2)
        acs <- List(addedChunks2)
        restPreChunks = (goal.pre.sigma.chunks.toSet -- callSubPre.sigma.chunks.toSet) ++ acs.chunks
        restPre = Assertion(goal.pre.phi && callPost.phi, mkSFormula(restPreChunks.toList))
        callGoal = goal.spawnChild(restPre, env = newEnv)
      } yield callGoal
    }
  }

  /*
   * The rule implementing a limited form of abduction:
   * Relaxes the function by replacing some of the points-to values by ghosts to allow for more unifications
   * Infers the discrepancies and emits new write-goals
   * Uses multiple-sub-derivation mechanism to enable several writes, followed by a call (via CallRule)
   */
  object AbduceCall extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "AbduceCall"

    // TODO: refactor common parts with CallRule
    def apply(goal: Goal): Seq[RuleResult] = {
      val allCands = goal.companionCandidates.reverse
      val cands = if (goal.env.config.auxAbduction) allCands else allCands.take(1)
      val fpecs = cands.map(_.toFunSpec) ++ // companions
        goal.env.functions.values // components
      for {
        _f <- fpecs
        // Make a "relaxed" substitution for the spec
        fStrict = _f.refreshExistentials(goal.vars)
        (f, exSub) = fStrict.relaxFunSpec

        lilHeap = f.pre.sigma
        largHeap = goal.pre.sigma
        matchingHeaps = findLargestMatchingHeap(f.pre.sigma, largHeap)
        largPreSubHeap <- matchingHeaps
        callSubPre = goal.pre.copy(sigma = largPreSubHeap) // A subheap of the precondition to unify with

        source = UnificationGoal(f.pre, f.params.map(_._2).toSet)
        target = UnificationGoal(callSubPre, goal.programVars.toSet)
        relaxedSub <- SpatialUnification.unify(target, source)
        // Preserve regular variables and fresh existentials back to what they were, if applicable
        actualSub = relaxedSub.filterNot { case (k, v) => exSub.keySet.contains(k) } ++ compose1(exSub, relaxedSub)
        if respectsOrdering(largPreSubHeap, lilHeap.subst(actualSub))
        if SMTSolving.valid(goal.pre.phi ==> f.pre.phi.subst(actualSub))
        (writeGoal, remainingGoal) <- writesAndRestGoals(actualSub, relaxedSub, f, goal)
      } yield {
        val kont = seqComp >> handleGuard(goal) >> extractHelper(goal)
        RuleResult(List(writeGoal, remainingGoal), kont, Footprint(largPreSubHeap, emp), this)
      }
    }

    def writesAndRestGoals(actualSub: Subst, relaxedSub: Subst, f: FunSpec, goal: Goal): Option[(Goal, Goal)] = {
      val ptss = f.pre.sigma.ptss // raw points-to assertions
      val (ptsToReplace, ptsToObtain) = (for {
        p@PointsTo(x@Var(_), off, e) <- ptss
        if actualSub.contains(x)
        if e.subst(relaxedSub) != e.subst(actualSub)
        actualSource = x.subst(actualSub)
        pToReplace <- goal.pre.sigma.ptss.find { case PointsTo(y, off1, _) => y == actualSource && off == off1 }
        pToObtain = PointsTo(actualSource, off, e.subst(actualSub))
      } yield {
        (pToReplace, pToObtain)
      }).unzip

      val heapAfterWrites = mkSFormula(((goal.pre.sigma.chunks.toSet -- ptsToReplace) ++ ptsToObtain).toList)
      if (ptsToReplace.isEmpty) None // No writes required
      else {
        // Writes required
        val writeGoalPre = Assertion(goal.pre.phi, mkSFormula(ptsToReplace))
        val writeGoalPost = Assertion(goal.pre.phi, mkSFormula(ptsToObtain))
        val writesGoal = goal.spawnChild(pre = writeGoalPre, post = writeGoalPost, childId = Some(0))
        val remainingGoal = goal.spawnChild(pre = Assertion(goal.pre.phi, heapAfterWrites), childId = Some(1))
        Some((writesGoal, remainingGoal))
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

    override def cost: Int = 1

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post
      val env = goal.env

      def heapletResults(h: Heaplet): Seq[RuleResult] = h match {
        case SApp(pred, args, Some(t)) =>
          if (t >= env.config.maxCloseDepth) return Nil

          ruleAssert(env.predicates.contains(pred),
            s"Close rule encountered undefined predicate: $pred")
          val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars)

          //ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val paramNames = params.map(_._2)
          val substArgs = paramNames.zip(args).toMap
          val subDerivations = for {
            InductiveClause(selector, asn) <- clauses
            // Make sure that existential in the body are fresh
            asnExistentials = asn.vars -- paramNames.toSet
            freshSuffix = args.take(1).map(_.pp).mkString("_")
            freshExistentialsSubst = refreshVars(asnExistentials.toList, goal.vars, freshSuffix)
            // Make sure that can unfold only once
            actualAssertion = asn.subst(freshExistentialsSubst).subst(substArgs)
            actualConstraints = actualAssertion.phi
            actualBody = actualAssertion.sigma.setUpSAppTags(t + 1, _ => true)
            // If we unfolded too much: back out
            //             if !actualBody.chunks.exists(h => exceedsMaxDepth(h))
          } yield {
            val actualSelector = selector.subst(freshExistentialsSubst).subst(substArgs)
            val newPhi = post.phi && actualConstraints && actualSelector
            val newPost = Assertion(newPhi, goal.post.sigma ** actualBody - h)

            val kont = idProducer >> handleGuard(goal) >> extractHelper(goal)

            RuleResult(List(goal.spawnChild(post = newPost)), kont, Footprint(emp, singletonHeap(h)), this)
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
