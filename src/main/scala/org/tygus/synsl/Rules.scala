package org.tygus.synsl

import org.tygus.synsl.LanguageUtils.generateFreshVar
import org.tygus.synsl.language.Expressions.{PConst, Var, Ident}
import org.tygus.synsl.language.Statements
import org.tygus.synsl.logic.Specifications
import org.tygus.synsl.logic.Declarations.Environment

/**
  * An implementation of a rule for synthesis
  *
  * @author Ilya Sergey
  */

trait Rules {

  import Specifications._
  import Statements._

  type Pre = Assertion
  type Post = Assertion

  // A continuation for synthesizing the "larger" statement from substatement
  type StmtProducer = Seq[Statement] => Statement

  abstract sealed class RuleResult

  /**
    * Rule is not applicable
    */
  case class Fail() extends RuleResult

  /**
    * Rule is applicable and produces:
    * - a sequence of subgoals (premises fo the rule)
    * - a producer: continuation that combines the results of the subgoals into the final statement
    * An empty list of subgoals paired with an constant producer denotes a leaf in the synthesis derivation
    */
  case class MoreGoals(goals: Seq[Spec], kont: StmtProducer) extends RuleResult

  /**
    * A generic class for a deductive rule to be applied
    */
  abstract sealed class Rule extends RuleUtils {
    // Apply the rule and get the subgoals
    def apply(spec: Spec, env: Environment): RuleResult

  }

  ///////////////////////////////////////////////////////////////////
  ///////////              Specific rules                     ///////
  ///////////////////////////////////////////////////////////////////

  /*
  Empty rule: supposed to be applied at the end

                  P |- Q
      ---------------------------------------- [emp]
      Γ ; { true; P } ; { true; Q } ---> return;
  */

  object EmpRule extends Rule {

    override def toString: Ident = "[emp]"

    def apply(spec: Spec, env: Environment): RuleResult = {
      // TODO: add value-returning statements
      if (spec.pre.sigma.isEmp && spec.post.sigma.isEmp)
        MoreGoals(Nil, _ => {Return(None)})
      else Fail()
    }
  }


  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{ φ ; x -> A * P } ; [y/A]{ ψ ; Q } ---> S
      ---------------------------------------------------------------------- [read]
              Γ ; { φ ; x -> A * P } ; { ψ ; Q } ---> let y := *x ; S
  */
  object ReadRule extends Rule {

    override def toString: Ident = "[read]"

    def apply(spec: Spec, env: Environment): RuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(_, _, a@(Var(_))) => spec.isGhost(a)
        case _ => false
      }

      findHeaplet(isGhostPoints, spec.pre.sigma) match {
        case None => Fail()
        case Some(PointsTo(x, offset, a@(Var(_)))) => {
          val y = generateFreshVar(spec, a.name)

          assert(spec.getType(a).nonEmpty, s"Cannot derive a type for the ghost variable $a in spec ${spec.pp}")
          val tpy = spec.getType(a).get

          val subGoalSpec = Spec(pre.subst(a, y), post.subst(a, y), (tpy, y) :: gamma.toList)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Read rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            // Do not generate read for unused variables
            if (rest.usedVars.contains(y)) Load(y, tpy, x, offset, rest) else rest
          }

          MoreGoals(Seq(subGoalSpec), kont)
        }
        case Some(h) => {
          assert(false, s"Read rule matched unexpected heaplet ${h.pp}")
          Fail()
        }
      }
    }
  }

  /*
  Write rule: create a new write from where it's possible

                      Γ ; { φ ; P } ; { ψ ; Q } ---> S
      -------------------------------------------------------------- [write]
       Γ ; { φ ; x -> e1 * P } ; { ψ ; x -> e2 * Q } ---> *x := e2 ; S
   */
  object WriteRule extends Rule {

    override def toString: Ident = "[write]"

    def apply(spec: Spec, env: Environment): RuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isConcretePoints: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.forall(v => spec.isConcrete(v))
        case _ => false
      }

      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && isConcretePoints(hr)

      findMatchingHeaplets(isConcretePoints, isMatch, spec.pre.sigma, spec.post.sigma) match {
        case None => Fail()
        case Some((hl@(PointsTo(x, offset, e1)), hr@(PointsTo(_, _, e2)))) => {
          val newPre = Assertion(pre.phi, spec.pre.sigma.remove(hl))
          val newPost = Assertion(post.phi, spec.post.sigma.remove(hr))
          val subGoalSpec = Spec(newPre, newPost, gamma)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Write rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            Store(x, offset, e2, rest)
          }

          MoreGoals(Seq(subGoalSpec), kont)
        }
        case Some((hl, hr)) => {
          assert(false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Fail()
        }
      }
    }

  }

  /*
  Alloc rule: allocate memory for an existential block

          X ∈ GV(post) / GV (pre)        y is fresh
       Γ ; { φ ; y -> (_0 .. _n) * P } ; { ψ ; [y/X]Q } ---> S
  ------------------------------------------------------------------ [alloc]
  Γ ; { φ ; P } ; { ψ ; block(X, n) * Q } ---> let y = malloc(n); S
  */
  object AllocRule extends Rule {

    override def toString: Ident = "[alloc]"

    def apply(spec: Spec, env: Environment): RuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isExistBlock(spec: Spec): Heaplet => Boolean = {
        case Block(v, _) => spec.isExistential(v)
        case _ => false
      }

      findHeaplet(isExistBlock(spec), spec.post.sigma) match {
        case None => Fail()
        case Some(h@(Block(x, sz))) => {
          val newPost = Assertion(spec.post.phi, spec.post.sigma.remove(h))
          val y = generateFreshVar(spec, x.name)

          assert(spec.getType(x).nonEmpty, s"Cannot derive a type for the ghost variable $x in spec ${spec.pp}")
          val tpy = spec.getType(x).get

          // TODO: replace 0 with blank
          val freshChunks = for (off <- 0 until sz) yield PointsTo(y, off, PConst(0))
          val newPre = Assertion(spec.pre.phi, SFormula(spec.pre.sigma.chunks ++ freshChunks))
          val subGoalSpec = Spec(newPre, newPost.subst(x, y), (tpy, y) :: gamma.toList)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Alloc rule expected 1 premise and got ${stmts.length}")
            Alloc(y, tpy, sz, stmts.head)
          }

          MoreGoals(Seq(subGoalSpec), kont)
        }
        case Some(h) =>
          assert(false, s"Alloc rule matched unexpected heaplet ${h.pp}")
          Fail()
      }
    }

  }

  /*
  Free rule: free a block from the pre-state if the post-state is emp

                        Γ ; { φ ; P } ; { ψ ; emp } ---> S
  ------------------------------------------------------------------------------- [free]
   Γ ; { φ ; block(x, n + 1) * x -> (e0 .. en) * P } ; { ψ ; emp } ---> free(x); S
*/
  object FreeRule extends Rule {

    override def toString: Ident = "[free]"

    def apply(spec: Spec, env: Environment): RuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isConcreteBlock: Heaplet => Boolean = {
        case Block(v, _) => spec.isConcrete(v)
        case _ => false
      }

      if (post.sigma.isEmp) {
        findHeaplet(isConcreteBlock, spec.pre.sigma) match {
          case None => Fail()
          case Some(h@Block(x, sz)) => {
            val pts = for (off <- 0 until sz) yield {
              findHeaplet(sameLhs(PointsTo(x, off, PConst(0))), spec.pre.sigma) match {
                case Some(pt) => pt
                case None => return Fail()
              }
            }
            val newPre = Assertion(spec.pre.phi, spec.pre.sigma.remove(h).remove(pts.toSet))
            val subGoalSpec = Spec(newPre, post, gamma)
            val kont: StmtProducer = stmts => {
              assert(stmts.lengthCompare(1) == 0, s"Free rule expected 1 premise and got ${stmts.length}")
              Free(x, stmts.head)
            }

            MoreGoals(Seq(subGoalSpec), kont)
          }
          case Some(h) =>
            assert(false, s"Free rule matched unexpected heaplet ${h.pp}")
            Fail()
        }
      } else Fail()
    }

  }


  /*
  Frame rule: reduce the size of the specification
  TODO: generalize from just heaplets

        (GV(Q) / GV(P)) ∪ GV(R) = Ø
      Γ ; { φ ; P } ; { ψ ; Q } ---> S
    ---------------------------------------- [frame]
    Γ ; { φ ; P * R } ; { ψ ; Q * R } ---> S

   */
  object FrameRule extends Rule {

    override def toString: Ident = "[frame]"

    def apply(spec: Spec, env: Environment): RuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      // TODO: better side condition: it's okay to remove heaplets with ghosts as long as it doesn't make things unreachable
      def isMatch(hl: Heaplet, hr: Heaplet) = hl.vars.forall(spec.isConcrete) && (hl |- hr)

      findMatchingHeaplets(Function.const(true), isMatch, spec.pre.sigma, spec.post.sigma) match {
        case None => Fail()
        case Some((hl, hr)) =>
          val newPre = Assertion(pre.phi, spec.pre.sigma.remove(hl))
          val newPost = Assertion(post.phi, spec.post.sigma.remove(hr))

          val subGoalSpec = Spec(newPre, newPost, gamma)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Frame rule expected 1 premise and got ${stmts.length}")
            stmts.head
          }

          MoreGoals(Seq(subGoalSpec), kont)
      }
    }

  }


}

