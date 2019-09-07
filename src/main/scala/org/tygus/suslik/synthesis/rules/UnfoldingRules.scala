package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.{Ident, Substitution, VoidType}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.unification.{SpatialUnification, UnificationGoal}
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules.{extractHelper, _}

/**
  * Unfolding rules deal with predicates and recursion.
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

object UnfoldingRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unfolding"

  object Open extends SynthesisRule with UnfoldingPhase {

    override def toString: Ident = "[Unfold: open]"

    // Produces a conditional that branches on the selectors
    private def branchProducer(selectors: Seq[PFormula]): StmtProducer = StmtProducer (
      selectors.length,
      liftToSolutions (stmts => {
        if (stmts.length == 1) stmts.head else {
          val cond_branches = selectors.zip(stmts).reverse
          val ctail = cond_branches.tail
          val finalBranch = cond_branches.head._2
          ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => If(c, tb, eb).simplify }
        }
      }),
      "open"
    )


    private def mkInductiveSubGoals(goal: Goal, h: Heaplet): Option[(Seq[(PFormula, Goal)], Heaplet)] = {
      val pre = goal.pre
      val env = goal.env

     //if (h.isAbsent) return None // TODO [Immutability] correct?

      h match {
        case x@SApp(pred, args, Some(t), mut, submut) if t < env.config.maxOpenDepth =>
          ruleAssert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")
          val predicate = env.predicates(pred)
          val InductivePredicate(_, params, clauses) = predicate.refreshExistentials(goal.vars)

          // here, we should check the params and change their tags... all of them
          // params need to be U(n) TODO [Immutability]
          // hm, we got the body from the predicate, so...

          val sbst = params.map(_._2).zip(args).toMap
          val remainingSigma = pre.sigma - h
          val newGoals = for {
            c@InductiveClause(_sel, _asn) <- clauses
            sel = _sel.subst(sbst)
            asn = _asn.subst(sbst)
            constraints = asn.phi
            body = asn.sigma
            // if our heaplet was not immutable, our opening must be immutable also


            // Adapt immutability for the clause to be substituted to the precondition
            predChunks = x.applyFineGrainedTags(x.submut, body.chunks)
            newPrePhi = mkConjunction(List(sel, pre.phi, constraints))
            // The tags in the body should be one more than in the current application:
            _newPreSigma1 = SFormula(predChunks).setUpSAppTags(t + 1)
            newPreSigma = _newPreSigma1 ** remainingSigma
          } yield (sel, goal.spawnChild(Assertion(newPrePhi, newPreSigma), childId = Some(clauses.indexOf(c))))
          // This is important, otherwise the rule is unsound and produces programs reading from ghosts
          // We can make the conditional without additional reading
          // TODO: Generalise this in the future
          val noGhosts = newGoals.forall { case (sel, _) => sel.vars.subsetOf(goal.programVars.toSet) }
          // TODo can absents be ghosts?
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
            Some(RuleResult(subGoals, kont))
        }
      } yield s
    }
  }

  /*
  Application rule: apply the inductive hypothesis

  TODO: Make sure it works on non-trivial sub-heaps
   */

  object CallRule extends SynthesisRule with UnfoldingPhase {

    override def toString: Ident = "[Unfold: call]"

    def apply(goal: Goal): Seq[RuleResult] = {
      // look at all proper ancestors starting from the root
      // and try to find a companion
      // (If auxiliary abduction is disabled, only look at the root)
      val allCands = goal.companionCandidates.reverse
      val cands = if (goal.env.config.auxAbduction) allCands else allCands.take(1)
      val funLabels = cands.map(a => (a.toFunSpec, Some(a.label))) ++ // companions
        goal.env.functions.values.map (f => (f, None)) // components
      for {
        (_f, l) <- funLabels
        f = _f.refreshExistentials(goal.vars)

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
        val kont: StmtProducer = prepend(Call(None, Var(f.name), args, l), toString) >> handleGuard(goal) >> extractHelper(goal)
        RuleResult(List(callGoal), kont)
      }
    }

    /**
      * Make a call goal for `f` with a given precondition
      */
    def mkCallGoal(f: FunSpec, sub: Substitution, callSubPre: Assertion, goal: Goal): List[Goal] = {
      val preFootprint = callSubPre.sigma.chunks.map(p => goal.hist.preIndex.lastIndexOf(p)).toSet
      val ruleApp = saveApplication((preFootprint, Set.empty), goal.hist)
      val callPost = f.post.subst(sub)

      /* added starts */
      val callPre = f.pre.subst(sub)
      // todo don't need a diff -- it's fine to apply to all heaplets
      //val diff = callPost.sigma.chunks.filterNot(callPre.sigma.chunks.toSet)
      //val diffEtc = SFormula(f.post.sigma.chunks.filterNot(f.pre.sigma.chunks.toSet))
      //diffEtc.subst(sub)
      //val diff = diffEtc.chunks

      val permissionedCallPost = SFormula(callPost.sigma.chunks.map((h : Heaplet) => {
        //if (diff.contains(h)) {
          // we need to find the corresponding heaplet in the callSubPre and f.pre
          // the pre and post should use the same variables
          def findCorrespondingHeaplets[T <: Heaplet](inner : Heaplet): Boolean =
            h match {
              case _ : PointsTo => inner.isInstanceOf[PointsTo] && inner.vars == h.vars
              case _ : Block => inner.isInstanceOf[Block] && inner.vars == h.vars
              case _ : SApp => inner.isInstanceOf[SApp] && inner.vars == h.vars
            }

          val callSubPreSubbed : SFormula = callSubPre.sigma subst sub

          val allPreHeapSubbed = callPre.sigma.chunks.filter(findCorrespondingHeaplets)
          if (allPreHeapSubbed.nonEmpty) {
            val preHeap = allPreHeapSubbed.head // assumung only one
            // there should be a matching one, otherwise synthesis would fail
            // TODO
            val allCallSubPreHeapSubbed = callSubPreSubbed.chunks.filter(findCorrespondingHeaplets) // assuming only one
            if (allCallSubPreHeapSubbed.nonEmpty) {
              val preHeapSubbed = allCallSubPreHeapSubbed.head

              // h should be weaker or equal to i.e. abs < imm < mut than the preheap
              assert(MTag.pre(preHeap.mut, h.mut)) // make sure that the returned permission is equal to or weaker than

              // TODO using the post here
              // will unify later?
              val newPermission = MTag.demote(preHeapSubbed.mut, preHeap.mut);
              h match {
                case PointsTo(a, b, c, d) => PointsTo(a, b, c, mut = newPermission)
                case Block(a, b, c) => Block(a, b, mut = newPermission)
                case SApp(a, b, c, d, e) => SApp(a, b, c, mut = newPermission, e)
                case _ => h
              }
            } else h
          } else h
      //  } else h
      }))

      /* added ends */

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
        restPre = Assertion(goal.pre.phi && callPost.phi, SFormula(restPreChunks.toList))
        callGoal = goal.spawnChild(restPre, newRuleApp = Some(ruleApp), env = newEnv)
      } yield callGoal
    }
  }

  /*
   * The rule implementing a limited form of abduction:
   * Relaxes the function by replacing some of the points-to values by ghosts to allow for more unifications
   * Infers the discrepancies and emits new write-goals
   * Uses multiple-sub-derivation mechanism to enable several writes, followed by a call (via CallRule)
   */
  object AbduceCall extends SynthesisRule with UnfoldingPhase {

    override def toString: Ident = "[Unfold: abduce-call]"

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
        actualSub = relaxedSub.filterNot { case (k, v) => exSub.keyset.contains(k) } ++ compose1(exSub, relaxedSub)
        if respectsOrdering(largPreSubHeap, lilHeap.subst(actualSub))
        if SMTSolving.valid(goal.pre.phi ==> f.pre.phi.subst(actualSub))
        (writeGoal, remainingGoal) <- writesAndRestGoals(actualSub, relaxedSub, f, goal)
      } yield {
        val kont = seqComp("abduce-call") >> handleGuard(goal) >> extractHelper(goal)
        RuleResult(List(writeGoal, remainingGoal), kont)
      }
    }

    def writesAndRestGoals(actualSub: Substitution, relaxedSub: Substitution, f: FunSpec, goal: Goal): Option[(Goal, Goal)] = {
      val ptss = f.pre.sigma.ptss // raw points-to assertions
      val (ptsToReplace, ptsToObtain) = (for {
        p@PointsTo(x@Var(_), off, e, _) <- ptss
        if actualSub.contains(x)
        if e.subst(relaxedSub) != e.subst(actualSub)
        actualSource = x.subst(actualSub)
        pToReplace <- goal.pre.sigma.ptss.find { case PointsTo(y, off1, _, _) => y == actualSource && off == off1 }
        pToObtain = PointsTo(actualSource, off, e.subst(actualSub))
      } yield {
        (pToReplace, pToObtain)
      }).unzip

      val heapAfterWrites = SFormula(((goal.pre.sigma.chunks.toSet -- ptsToReplace) ++ ptsToObtain).toList)
      if (ptsToReplace.isEmpty) None // No writes required
      else {
        // Writes required
        val writeGoalPre = Assertion(goal.pre.phi, SFormula(ptsToReplace))
        val writeGoalPost = Assertion(goal.pre.phi, SFormula(ptsToObtain))
        val writesGoal = goal.spawnChild(pre = writeGoalPre, post = writeGoalPost, childId = Some(0))
        val remainingGoal = goal.spawnChild(pre = Assertion(goal.pre.phi, heapAfterWrites), childId = Some(1))
        Some((writesGoal, remainingGoal))
      }
      // val preFootprintToReplace = ptsToReplace.map(p => goal.deriv.preIndex.indexOf(p)).toSet
      // val ruleApp = saveApplication((preFootprintToReplace, Set.empty), goal.deriv)
    }
  }

  /*
  Close rule: unroll a predicate in the post-state

              p(params) := { true ? b }
    Γ ; { φ ; P } ; { ψ ; b[args/params] * Q } ---> S
    ---------------------------------------------------- [close]
        Γ ; { φ ; P } ; { ψ ; p(args) * Q } ---> S

   */
  object Close extends SynthesisRule with UnfoldingPhase {

    override def toString: Ident = "[Unfold: close]"

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post
      val env = goal.env
      val deriv = goal.hist

      // Does h have a tag that exceeds the maximum allowed unfolding depth?
      def exceedsMaxDepth(h: Heaplet): Boolean = {
        h match {
          case SApp(_, _, Some(t), _, _) => t > env.config.maxCloseDepth
          case _ => false
        }
      }

      def hasImmutablePreCounterpart(h : Heaplet) : Boolean = {
        goal.pre.sigma.chunks.foldLeft[Boolean](true)((acc: Boolean, h1 : Heaplet) =>
          if (h.lhsVars.intersect(h1.lhsVars).nonEmpty) { acc && h1.isImmutable } else acc)
      }

      def heapletResults(h: Heaplet): Seq[RuleResult] = h match {
        case x@SApp(pred, args, Some(t), _, _) =>
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
            freshExistentialsSubst = refreshVars(asnExistentials.toList, goal.vars)
            // Make sure that can unfold only once
            actualAssertion = asn.subst(freshExistentialsSubst).subst(substArgs)
            actualConstraints = actualAssertion.phi
            actualBody = actualAssertion.sigma.setUpSAppTags(t + 1, _ => true)
            // If we unfolded too much: back out
            //             if !actualBody.chunks.exists(h => exceedsMaxDepth(h))
            predChunks = //if (h.isImmutable && x.submut.isEmpty) {
              //actualBody.copy(actualBody.chunks.map (c => c.mkImmutable))
            //} else {
              actualBody.copy(x.applyFineGrainedTags(x.submut, actualBody.chunks))
            //}

          } yield {
            val actualSelector = selector.subst(freshExistentialsSubst).subst(substArgs)
            val newPhi = mkConjunction(List(actualSelector, post.phi, actualConstraints))
            val newPost = Assertion(newPhi, goal.post.sigma ** predChunks - h)

            val postFootprint = Set(deriv.postIndex.lastIndexOf(h))
            val ruleApp = saveApplication((Set.empty, postFootprint), deriv)
            val kont = idProducer("close") >> handleGuard(goal) >> extractHelper(goal)

            RuleResult(List(goal.spawnChild(post = newPost, newRuleApp = Some(ruleApp))), kont)
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
