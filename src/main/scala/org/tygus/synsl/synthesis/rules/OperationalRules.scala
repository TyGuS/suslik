package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.LanguageUtils.generateFreshVar
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.{Statements, _}
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis._

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

object OperationalRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-operational"

  import Statements._

  // TODO: Implement [cond]
  // TODO: Implement [call]


  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; x.f -> l' * P} ; {ψ ; x.f -> l' * Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l' * Q} ---> *x.f := l' ; S

  */
  object WriteRuleOld extends SynthesisRule {

    override def toString: Ident = "[Op: write]"

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      val Goal(pre, post, gamma: Gamma, fname) = goal

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && noGhosts(hr)

      findMatchingHeaplets(noGhosts, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => SynFail
        case Some((hl@(PointsTo(x@Var(_), offset, e1)), hr@(PointsTo(_, _, e2)))) =>
          if (e1 == e2) { return SynFail } // Do not write if RHSs are the same

          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi, goal.post.sigma - hr)
          val subGoal = Goal(newPre, newPost, gamma, fname)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Write rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            SeqComp(Store(x, offset, e2), rest)
          }

          SynAndGoals(Seq((subGoal, env)), kont)
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          SynFail
      }
    }

  }

  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; P} ; {ψ ; x.f -> Y * Q} ---> S   GV(l) = Ø  Y is fresh
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; P} ; {ψ ; x.f -> l * Q} ---> S; *x.f := l

  */
  object WriteRule extends SynthesisRule {

    override def toString: Ident = "[Op: write]"

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      val Goal(pre, post, gamma, fname) = goal

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      findHeaplet(noGhosts, post.sigma) match {
        case None => SynFail
        case Some(h@(PointsTo(x@Var(_), offset, l))) =>
          val y = generateFreshVar(goal)

          val newPost = Assertion (post.phi, (post.sigma - h) ** PointsTo(x, offset, y))
          val subGoal = Goal(pre, newPost, gamma, fname)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Write rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            SeqComp(rest, Store(x, offset, l))
          }
          SynAndGoals(Seq((subGoal, env)), kont)
        case Some(h) =>
          ruleAssert(false, s"Write rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }
  }

  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{φ ; x -> A * P} ; [y/A]{ψ ; Q} ---> S
      ---------------------------------------------------------------- [read]
             Γ ; {φ ; x.f -> A * P} ; {ψ ; Q} ---> let y := *x.f ; S
  */
  object ReadRule extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "[Op: read]"

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      val Goal(pre, post, gamma, fname) = goal

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, a@(Var(_))) => goal.isGhost(a) && !goal.isGhost(x)
        case _ => false
      }

      findHeaplet(isGhostPoints, goal.pre.sigma) match {
        case None => SynFail
        case Some(PointsTo(x@Var(_), offset, a@(Var(_)))) =>
          val y = generateFreshVar(goal, a.name)
          val tpy = goal.getType(a)

          val subGoal = Goal(pre.subst(a, y), post.subst(a, y), (tpy, y) :: gamma.toList, fname)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Read rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            // Do not generate read for unused variables
            if (rest.usedVars.contains(y)) SeqComp (Load(y, tpy, x, offset), rest) else rest
          }

          SynAndGoals(Seq((subGoal, env)), kont)
        case Some(h) =>
          ruleAssert(false, s"Read rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }
  }

  /*
  Alloc rule: allocate memory for an existential block

           X ∈ GV(post) / GV (pre)        y, Ai fresh
         Γ ; {φ ; y -> (A0 .. An) * P} ; {ψ ; [y/X]Q} ---> S
     -------------------------------------------------------------- [alloc]
     Γ ; {φ ; P} ; {ψ ; block(X, n) * Q} ---> let y = malloc(n); S
  */
  object AllocRule extends SynthesisRule {

    override def toString: Ident = "[Op: alloc]"

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      val Goal(pre, post, gamma: Gamma, fname) = goal

      def isExistBlock(goal: Goal): Heaplet => Boolean = {
        case Block(x@Var(_), _) => goal.isExistential(x)
        case _ => false
      }

      findHeaplet(isExistBlock(goal), post.sigma) match {
        case None => SynFail
        case Some(h@(Block(x@Var(_), sz))) =>
          val newPost = Assertion(post.phi, post.sigma - h)
          val y = generateFreshVar(goal, x.name)
          val tpy = LocType

          // TODO: replace 0 with blank
          val freshChunks = for (off <- 0 until sz) yield PointsTo(y, off, IntConst(0))
          val newPre = Assertion(pre.phi, SFormula(pre.sigma.chunks ++ freshChunks))
          val subGoal = Goal(newPre, newPost.subst(x, y), (tpy, y) :: gamma.toList, fname)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Alloc rule expected 1 premise and got ${stmts.length}")
            SeqComp(Malloc(y, tpy, sz), stmts.head)
          }

          SynAndGoals(Seq((subGoal, env)), kont)
        case Some(h) =>
          ruleAssert(false, s"Alloc rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }

  }

  /*
  Free rule: free a non-ghost block from the pre-state

                     Γ ; {φ ; P} ; {ψ ; Q} ---> S     GV(li) = Ø
   ------------------------------------------------------------------------ [free]
   Γ ; {φ ; block(x, n) * x -> (l1 .. ln) * P} ; { ψ ; Q } ---> free(x); S
*/
  object FreeRule extends SynthesisRule {

    override def toString: Ident = "[Op: free]"

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      val Goal(_, post, gamma: Gamma, fname) = goal

      def isConcreteBlock: Heaplet => Boolean = {
        case Block(v@(Var(_)), _) => goal.isConcrete(v)
        case _ => false
      }

      findHeaplet(isConcreteBlock, goal.pre.sigma) match {
        case None => SynFail
        case Some(h@Block(x@(Var(_)), sz)) =>
          // Okay, found the block, now looking for the points-to chunks
          val pts = for (off <- 0 until sz) yield {
            findHeaplet(sameLhs(PointsTo(x, off, IntConst(0))), goal.pre.sigma) match {
              case Some(pt) if pt.vars.forall(!goal.isGhost(_)) => pt
              case _ => return SynFail
            }
          }
          val newPre = Assertion(goal.pre.phi, goal.pre.sigma - h - pts)
          val subGoal = Goal(newPre, post, gamma, fname)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Free rule expected 1 premise and got ${stmts.length}")
            SeqComp(Free(x), stmts.head)
          }

          SynAndGoals(Seq((subGoal, env)), kont)
        case Some(h) =>
          ruleAssert(false, s"Free rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }

  }

}

