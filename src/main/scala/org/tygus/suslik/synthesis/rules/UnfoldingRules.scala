package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.{Ident, Substitution, VoidType}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.unification.{SpatialUnification, UnificationGoal}
import org.tygus.suslik.synthesis._

/**
  * Unfolding rules deal with predicates and recursion.
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

object UnfoldingRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unfolding"

  object Open extends SynthesisRule with UnfoldingPhase {

    override def toString: Ident = "[Unfold: open]"

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
          // other things?
          val remainingChunks = pre.sigma.chunks.filter(_ != h)
          val newGoals = for {
            // each clause is like a case of a one-of
            InductiveClause(_sel, _asn) <- clauses
            sel = _sel.subst(sbst)
            asn = _asn.subst(sbst)
            constraints = asn.phi
            body = asn.sigma
            // if our heaplet was not immutable, our opening must be immutable also


            predChunks = //if (h.isImmutable && submut.isEmpty) {
              //body.chunks.map (c => c.mkImmutable)
            //} else {
              // Instantiate immutability tag in a clause's body via client-side annotations
              x.applyFineGrainedTags(x.submut, body.chunks)
            //}

            newPrePhi = mkConjunction(List(sel, pre.phi, constraints))
            _newPreSigma1 = SFormula(predChunks).bumpUpSAppTags()
            // we don't care about other heaps in the pre/post, only these
            _newPreSigma2 = SFormula(remainingChunks).lockSAppTags()
            newPreSigma = SFormula(_newPreSigma1.chunks ++ _newPreSigma2.chunks)
          } yield (sel, goal.copy(Assertion(newPrePhi, newPreSigma)): Goal)
          // This is important, otherwise the rule is unsound and produces programs reading from ghosts
          // We can make the conditional without additional reading
          // TODO: Generalise this in the future
          val noGhosts = newGoals.forall { case (sel, _) => sel.vars.subsetOf(goal.programVars.toSet) }
          // TODo can absents be ghosts?
          if (noGhosts) Some((newGoals, h)) else None
        case _ => None
      }
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      for {
        h <- goal.pre.sigma.chunks
        s <- mkInductiveSubGoals(goal, h) match {
          case None => None
          case Some((selGoals, h)) =>
            val (selectors, subGoals) = selGoals.unzip
            Some(Subderivation(subGoals, kont(selectors)))
        }
      } yield s
    }
  }

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
  object InductionRule extends SynthesisRule with AnyPhase {

    override def toString: Ident = "[Unfold: induction]"

    private def mkIndHyp(goal: Goal, h: Heaplet): Environment = {
      val env = goal.env
      val fname = Var(goal.fname).refresh(env.functions.keySet.map(Var)).name
      // TODO: provide a proper type, not VOID

      // Re-tagging all predicate occurrences, so the inductive argument
      // would be tagged with Some(1), and everyone else with None(1)
      val SApp(pname, xs, t, _, _) = h
      val matcher: Heaplet => Boolean = {
        case SApp(x, ys, q, _, _) => x == pname && ys == xs
        case _ => false
      }
      val newPre = goal.pre.bumpUpSAppTags(matcher).lockSAppTags(x => !matcher(x))
      // TODO: If we want to apply IH more than once to the same heap, we need to produce several copies of the hypothesis with increasing tags
      // Second-order, now can only apply library functions
      val newPost = goal.post.bumpUpSAppTags()

      val fspec = FunSpec(fname, VoidType, goal.formals, newPre, newPost)
      env.copy(functions = env.functions + (fname -> fspec))
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      val env = goal.env
      if (env.functions.keySet.contains(goal.fname)) return Nil
      // TODO: this is a hack to avoid invoking induction where it has no chance to succeed
      if (goal.hasAllocatedBlocks) return Nil
      val preApps = goal.pre.sigma.apps
      // Nothing to induce on
      if (preApps.isEmpty) return Nil

      val apps = preApps ++ goal.post.sigma.apps
      val noInductionOrUnfoldings = apps.forall {
        case SApp(_, _, t, _, _) => t.contains(0)
      }

      if (!noInductionOrUnfoldings) return Nil

      for {
        a <- preApps
        newEnv = mkIndHyp(goal, a)
        // TODO immutability
        newGoal = goal.copy(env = newEnv)
      } yield Subderivation(Seq(newGoal), pureKont(toString))
    }
  }

  /*
  Application rule: apply the inductive hypothesis

  TODO: Make sure it works on non-trivial sub-heaps
   */

  object CallRule extends SynthesisRule with UnfoldingPhase {

    override def toString: Ident = "[Unfold: call]"

    def apply(goal: Goal): Seq[Subderivation] = {
      (for {
        (_, _f) <- goal.env.functions
        f = _f.refreshExistentials(goal.vars)

        // Find all subsets of the goal's pre that might be unified
        lilHeap = f.pre.sigma
        largHeap = goal.pre.sigma
        largSubHeap <- findLargestMatchingHeap(lilHeap, largHeap)
        callSubPre = goal.pre.copy(sigma = largSubHeap)

        // Try to unify f's precondition and found goal pre's subheaps
        source = UnificationGoal(f.pre, f.params.map(_._2).toSet)
        target = UnificationGoal(callSubPre, goal.programVars.toSet)
        sub <- {
          SpatialUnification.unify(target, source).toList
        }
        if SMTSolving.valid(goal.pre.phi ==> f.pre.phi.subst(sub))
        args = f.params.map { case (_, x) => x.subst(sub) }
        if args.flatMap(_.vars).toSet.subsetOf(goal.vars)
        callGoal <- mkCallGoal(f, sub, callSubPre, goal)
      } yield {
        val kont: StmtProducer = prepend(Call(None, Var(f.name), args), toString)
        Subderivation(List(callGoal), kont)
      }).toSeq
    }

    /**
      * Make a call goal for `f` with a given precondition
      */
    def mkCallGoal(f: FunSpec, sub: Substitution, callSubPre: Assertion, goal: Goal): List[Goal] = {

      //val diff = f.post.sigma.chunks.foldLeft[Set[Heaplet]](Set.empty[Heaplet])((acc : Set[Heaplet], h: Heaplet) =>
      //if (f.pre.sigma.chunks.contains(h)) acc + h else acc) // post &~ pre (set difference)

      val preFootprint = callSubPre.sigma.chunks.map(p => goal.deriv.preIndex.lastIndexOf(p)).toSet
      val ruleApp = saveApplication((preFootprint, Set.empty), goal.deriv)
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
        // To avoind more than one application of a library function
        val funs = goal.env.functions.filterKeys(_ != f.name)
        goal.env.copy(functions = funs)
      }

      // check for each heaplet which matches against something in the call pre
      // update the post(?)


//      val addedChunks1 = callPost.sigma.bumpUpSAppTags()
//      val addedChunks2 = callPost.sigma.lockSAppTags()

      val addedChunks1 = permissionedCallPost.bumpUpSAppTags()
      val addedChunks2 = permissionedCallPost.lockSAppTags()


      // Here we return two options for added chunks:
      // (a) with bumped tags
      // (b) with locked tags
      // The former enables applications of other functions (tree-flatten)
      // The latter enables application of the same recursive function (tree-flatten-acc),
      // but "focused" on a different some(1)-tagged predicate applications. Both are sound.
      for {
        acs <- List(addedChunks1, addedChunks2)
        restPreChunks = (goal.pre.sigma.chunks.toSet -- callSubPre.sigma.chunks.toSet) ++ acs.chunks
        restPre = Assertion(goal.pre.phi && callPost.phi, SFormula(restPreChunks.toList))
        callGoal = goal.copy(restPre, newRuleApp = Some(ruleApp), env = newEnv)
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

    def apply(goal: Goal): Seq[Subderivation] = {
      (for {
        (_, _funSpec) <- goal.env.functions

        // Make a "relaxed" substitution for the spec and for with it
        (f, exSub) = _funSpec.refreshExistentials(goal.vars).relaxFunSpec

        lilHeap = f.pre.sigma
        largHeap = goal.pre.sigma
        matchingHeaps = findLargestMatchingHeap(lilHeap, largHeap)
        largPreSubHeap <- matchingHeaps
        callSubPre = goal.pre.copy(sigma = largPreSubHeap) // A subheap of the precondition to unify with

        source = UnificationGoal(f.pre, f.params.map(_._2).toSet)
        target = UnificationGoal(callSubPre, goal.programVars.toSet)
        relaxedSub <- SpatialUnification.unify(target, source)
        // Preserve regular variables and fresh existentials back to what they were, if applicable
        actualSub = relaxedSub.filterNot { case (k, v) => exSub.keyset.contains(k) } ++ compose1(exSub, relaxedSub)
        if SMTSolving.valid(goal.pre.phi ==> f.pre.phi.subst(actualSub))
        (writeGoalsOpt, restGoal) = writesAndRestGoals(actualSub, relaxedSub, f, goal)
        if writeGoalsOpt.nonEmpty
      } yield {
        val writeGoals = writeGoalsOpt.toList
        val n = writeGoals.length
        val kont: StmtProducer = stmts => {
          ruleAssert(stmts.length == n + 1, s"Apply-hypotheses rule expected ${n + 1} premise and got ${stmts.length}")
          val writes = stmts.take(n)
          val rest = stmts.drop(n).head
          writes.foldRight(rest) { case (w, r) => SeqComp(w, r) }
        }
        val subGoals = writeGoals ++ List(restGoal)
        Subderivation(subGoals, kont)
      }).toSeq
    }

    def writesAndRestGoals(actualSub: Substitution, relaxedSub: Substitution, f: FunSpec, goal: Goal): (Option[Goal], Goal) = {
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


      // val preFootprintToReplace = ptsToReplace.map(p => goal.deriv.preIndex.indexOf(p)).toSet
      // val ruleApp = saveApplication((preFootprintToReplace, Set.empty), goal.deriv)
      val heapAfterWrites = SFormula(((goal.pre.sigma.chunks.toSet -- ptsToReplace) ++ ptsToObtain).toList)
      val remainingGoal = goal.copy(pre = Assertion(goal.pre.phi, heapAfterWrites))

      if (ptsToReplace.isEmpty) return (None, remainingGoal)

      val smallWriteGoalPre = Assertion(goal.pre.phi, SFormula(ptsToReplace))
      val smallWriteGoalPost = Assertion(goal.pre.phi, SFormula(ptsToObtain))
      val smallWritesGoal = goal.copy(pre = smallWriteGoalPre, post = smallWriteGoalPost)

      (Some(smallWritesGoal), remainingGoal)
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

    private val kont: StmtProducer = stmts => {
      ruleAssert(stmts.lengthCompare(1) == 0, s"Close rule expected 1 premise and got ${stmts.length}")
      stmts.head
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      val post = goal.post
      val env = goal.env
      val deriv = goal.deriv

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

      def heapletResults(h: Heaplet): Seq[Subderivation] = h match {
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

            Subderivation(List(goal.copy(post = newPost, newRuleApp = Some(ruleApp))), kont)
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
