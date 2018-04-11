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
  object WriteRule extends SynthesisRule {

    override def toString: Ident = "[Op: write]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.forall(v => !spec.isGhost(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && noGhosts(hr)

      findMatchingHeaplets(noGhosts, isMatch, spec.pre.sigma, spec.post.sigma) match {
        case None => SynFail
        case Some((hl@(PointsTo(x@Var(_), offset, _)), hr@(PointsTo(_, _, e2)))) =>
          val newPre = Assertion(pre.phi, spec.pre.sigma - hl)
          val newPost = Assertion(post.phi, spec.post.sigma - hr)
          val subGoalSpec = Spec(newPre, newPost, gamma)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Write rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            Store(x, offset, e2, rest)
          }

          SynAndGoals(Seq(subGoalSpec), kont)
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
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
  object ReadRule extends SynthesisRule {

    override def toString: Ident = "[Op: read]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(_, _, a@(Var(_))) => spec.isGhost(a)
        case _ => false
      }

      findHeaplet(isGhostPoints, spec.pre.sigma) match {
        case None => SynFail
        case Some(PointsTo(x@Var(_), offset, a@(Var(_)))) =>
          val y = generateFreshVar(spec, a.name)
          val tpy = spec.getType(a)

          val subGoalSpec = Spec(pre.subst(a, y), post.subst(a, y), (tpy, y) :: gamma.toList)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Read rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            // Do not generate read for unused variables
            if (rest.usedVars.contains(y)) Load(y, tpy, x, offset, rest) else rest
          }

          SynAndGoals(Seq(subGoalSpec), kont)
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

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isExistBlock(spec: Spec): Heaplet => Boolean = {
        case Block(x@Var(_), _) => spec.isExistential(x)
        case _ => false
      }

      findHeaplet(isExistBlock(spec), post.sigma) match {
        case None => SynFail
        case Some(h@(Block(x@Var(_), sz))) =>
          val newPost = Assertion(post.phi, post.sigma - h)
          val y = generateFreshVar(spec, x.name)
          val tpy = LocType

          // TODO: replace 0 with blank
          val freshChunks = for (off <- 0 until sz) yield PointsTo(y, off, IntConst(0))
          val newPre = Assertion(pre.phi, SFormula(pre.sigma.chunks ++ freshChunks))
          val subGoalSpec = Spec(newPre, newPost.subst(x, y), (tpy, y) :: gamma.toList)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Alloc rule expected 1 premise and got ${stmts.length}")
            Malloc(y, tpy, sz, stmts.head)
          }

          SynAndGoals(Seq(subGoalSpec), kont)
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

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(_, post, gamma: Gamma) = spec

      def isConcreteBlock: Heaplet => Boolean = {
        case Block(v@(Var(_)), _) => spec.isConcrete(v)
        case _ => false
      }

      findHeaplet(isConcreteBlock, spec.pre.sigma) match {
        case None => SynFail
        case Some(h@Block(x@(Var(_)), sz)) =>
          // Okay, found the block, now looking for the points-to chunks
          val pts = for (off <- 0 until sz) yield {
            findHeaplet(sameLhs(PointsTo(x, off, IntConst(0))), spec.pre.sigma) match {
              case Some(pt) if pt.vars.forall(!spec.isGhost(_)) => pt
              case _ => return SynFail
            }
          }
          val newPre = Assertion(spec.pre.phi, spec.pre.sigma - h - pts)
          val subGoalSpec = Spec(newPre, post, gamma)
          val kont: StmtProducer = stmts => {
            ruleAssert(stmts.lengthCompare(1) == 0, s"Free rule expected 1 premise and got ${stmts.length}")
            Free(x, stmts.head)
          }

          SynAndGoals(Seq(subGoalSpec), kont)
        case Some(h) =>
          ruleAssert(false, s"Free rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }

  }

}

