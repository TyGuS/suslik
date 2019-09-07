package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.LanguageUtils.generateFreshVar
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{Statements, _}
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Operational rules emit statement that operate of flat parts of the heap.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object OperationalRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-operational"

  import Statements._

  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; x.f -> l' * P} ; {ψ ; x.f -> l' * Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l' * Q} ---> *x.f := l' ; S

  */
  object WriteRuleOld extends SynthesisRule with FlatPhase {

    override def toString: Ident = "[Op: write-old]"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e, _) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && noGhosts(hr)

      findMatchingHeaplets(noGhosts, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@PointsTo(x@Var(_), offset, e1, m1), hr@PointsTo(_, _, e2, m2))) =>
          if (e1 == e2) {
            return Nil
          } // Do not write if RHSs are the same

          if (!hl.isMutable || m1 != m2) {
            return Nil
            // Do not write if points-to is immutable
          }

          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi, goal.post.sigma - hr)
          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = prepend(Store(x, offset, e2), toString) >> handleGuard(goal) >> extractHelper(goal)

          List(RuleResult(List(subGoal), kont))
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }
  }


  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; P} ; {ψ ; x.f -> Y * Q} ---> S   GV(l) = Ø  Y is fresh
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; P} ; {ψ ; x.f -> l * Q} ---> S; *x.f := l

  */
  object WriteRule extends SynthesisRule with FlatPhase with InvertibleRule {

    override def toString: Ident = "[Op: write]"

    def apply(goal: Goal): Seq[RuleResult] = {

      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e, _) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      findHeaplet(noGhosts, post.sigma) match {
        case None => Nil
        case Some(h@PointsTo(x@Var(_), offset, l, _)) =>

          // Cannot write to immutable or absent heaplets
          if (!h.isMutable) return Nil

          // Same heaplet in pre: no point in writing
          if (pre.sigma.chunks.contains(h)) return Nil

          val y = generateFreshVar(goal)

          val newPost = Assertion(post.phi, (post.sigma - h) ** PointsTo(x, offset, y))
          val subGoal = goal.spawnChild(post = newPost)
          val kont: StmtProducer = append(Store(x, offset, l), toString) >> handleGuard(goal) >> extractHelper(goal)
          List(RuleResult(List(subGoal), kont))
        case Some(h) =>
          ruleAssert(false, s"Write rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }
  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{φ ; x -> A * P} ; [y/A]{ψ ; Q} ---> S
      ---------------------------------------------------------------- [read]
             Γ ; {φ ; x.f -> A * P} ; {ψ ; Q} ---> let y := *x.f ; S
  */
  object ReadRule extends SynthesisRule with AnyPhase with InvertibleRule {

    override def toString: Ident = "[Op: read]"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post
      val gamma = goal.gamma

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, a@Var(_), _) =>
          goal.isGhost(a) && !goal.isGhost(x)
        case _ => false
      }

      findHeaplet(isGhostPoints, goal.pre.sigma) match {
        case None => Nil
        case Some(h@PointsTo(x@Var(_), offset, a@Var(_), _)) =>

          val y = generateFreshVar(goal, a.name)
          val tpy = goal.getType(a)

          val subGoal = goal.spawnChild(pre.subst(a, y), post = post.subst(a, y)).addProgramVar(y,tpy)
          val kont: StmtProducer = prepend(Load(y, tpy, x, offset), toString) >> handleGuard(goal) >> extractHelper(goal)
          List(RuleResult(List(subGoal), kont))
        case Some(h) =>
          ruleAssert(false, s"Read rule matched unexpected heaplet ${h.pp}")
          Nil
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
  object AllocRule extends SynthesisRule with FlatPhase { // TODO should we guard?
    override def toString: Ident = "[Op: alloc]"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      def isExistBlock: Heaplet => Boolean = {
        case Block(x@Var(_), _, _) => goal.isExistential(x)
        case _ => false
      }

      findBlockAndChunks(isExistBlock, _ => true, goal.post.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = {

      val pre = goal.pre
      val post = goal.post
      val gamma = goal.gamma
      val deriv = goal.hist

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), sz, _), pts)) =>
          val y = generateFreshVar(goal, x.name)
          val tpy = LocType

          val freshChunks = for {
            off <- 0 until sz
            z = generateFreshVar(goal)
          } // yield PointsTo(y, off, z)
            yield PointsTo(y, off, IntConst(666))
          val freshBlock = Block(x, sz).subst(x, y)
          val newPre = Assertion(pre.phi, SFormula(pre.sigma.chunks ++ freshChunks ++ List(freshBlock)))

          val postFootprint = pts.map(p => deriv.postIndex.lastIndexOf(p)).toSet + deriv.postIndex.lastIndexOf(h)
          val ruleApp = saveApplication((Set.empty, postFootprint), deriv)

          val subGoal = goal.spawnChild(newPre, post.subst(x, y), newRuleApp = Some(ruleApp)).addProgramVar(y, tpy)
          val kont: StmtProducer = prepend(Malloc(y, tpy, sz), toString) >> handleGuard(goal) >> extractHelper(goal)
          List(RuleResult(List(subGoal), kont))
        case _ => Nil
      }
    }

  }

  /*
  Free rule: free a non-ghost block from the pre-state

                     Γ ; {φ ; P} ; {ψ ; Q} ---> S     GV(li) = Ø
   ------------------------------------------------------------------------ [free]
   Γ ; {φ ; block(x, n) * x -> (l1 .. ln) * P} ; { ψ ; Q } ---> free(x); S
*/
  object FreeRule extends SynthesisRule with FlatPhase {

    override def toString: Ident = "[Op: free]"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))

      findBlockAndChunks(noGhosts, noGhosts, goal.pre.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val deriv = goal.hist

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), _, _), pts)) =>
          // should not be allowed if the target heaplet is immutable
          if (!h.isMutable || pts.exists(z => !z.isMutable)) return Nil

          val newPre = Assertion(pre.phi, pre.sigma - h - pts)

          // Collecting the footprint
          val preFootprint = pts.map(p => deriv.preIndex.lastIndexOf(p)).toSet + deriv.preIndex.lastIndexOf(h)
          val ruleApp = saveApplication((preFootprint, Set.empty), deriv)

          val subGoal = goal.spawnChild(newPre, newRuleApp = Some(ruleApp))
          val kont: StmtProducer = prepend(Free(x), toString) >> handleGuard(goal) >> extractHelper(goal)

          List(RuleResult(List(subGoal), kont))
        case Some(_) => Nil
      }
    }

  }

}