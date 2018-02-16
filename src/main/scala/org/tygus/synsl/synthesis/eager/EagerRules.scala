package org.tygus.synsl.synthesis.eager

import org.tygus.synsl.LanguageUtils.generateFreshVar
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.{Statements, _}
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis.SynthesisRules

/**
  * An implementation of a rule for synthesis
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait EagerRules extends SynthesisRules {

  import Statements._

  ///////////////////////////////////////////////////////////////////
  ///////////              Specific rules                     ///////
  ///////////////////////////////////////////////////////////////////

  /*
  Empty rule: supposed to be applied at the end

                  P |- Q
      ---------------------------------------- [emp]
      Γ ; { true; P } ; { true; Q } ---> return;
  */

  object EmpRule extends SynthesisRule {

    override def toString: Ident = "[emp]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      // TODO: add value-returning statements
      if (spec.pre.sigma.isEmp && spec.post.sigma.isEmp)
        SynMoreGoals(Nil, _ => {Return(None)})
      else SynFail
    }
  }


  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{ φ ; x -> A * P } ; [y/A]{ ψ ; Q } ---> S
      ---------------------------------------------------------------------- [read]
              Γ ; { φ ; x -> A * P } ; { ψ ; Q } ---> let y := *x ; S
  */
  object ReadRule extends SynthesisRule {

    override def toString: Ident = "[read]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(_, _, a@(Var(_))) => spec.isGhost(a)
        case _ => false
      }

      findHeaplet(isGhostPoints, spec.pre.sigma) match {
        case None => SynFail
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

          SynMoreGoals(Seq(subGoalSpec), kont)
        }
        case Some(h) =>
          assert(assertion = false, s"Read rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }
  }

  /*
  Write rule: create a new write from where it's possible

                      Γ ; { φ ; P } ; { ψ ; Q } ---> S
      -------------------------------------------------------------- [write]
       Γ ; { φ ; x -> e1 * P } ; { ψ ; x -> e2 * Q } ---> *x := e2 ; S
   */
  object WriteRule extends SynthesisRule {

    override def toString: Ident = "[write]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isConcretePoints: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.forall(v => spec.isConcrete(v))
        case _ => false
      }

      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && isConcretePoints(hr)

      findMatchingHeaplets(isConcretePoints, isMatch, spec.pre.sigma, spec.post.sigma) match {
        case None => SynFail
        case Some((hl@(PointsTo(x, offset, e1)), hr@(PointsTo(_, _, e2)))) => {
          val newPre = Assertion(pre.phi, spec.pre.sigma - hl)
          val newPost = Assertion(post.phi, spec.post.sigma - hr)
          val subGoalSpec = Spec(newPre, newPost, gamma)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Write rule expected 1 premise and got ${stmts.length}")
            val rest = stmts.head
            Store(x, offset, e2, rest)
          }

          SynMoreGoals(Seq(subGoalSpec), kont)
        }
        case Some((hl, hr)) =>
          assert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          SynFail
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
  object AllocRule extends SynthesisRule {

    override def toString: Ident = "[alloc]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isExistBlock(spec: Spec): Heaplet => Boolean = {
        case Block(v, _) => spec.isExistential(v)
        case _ => false
      }

      findHeaplet(isExistBlock(spec), spec.post.sigma) match {
        case None => SynFail
        case Some(h@(Block(x, sz))) => {
          val newPost = Assertion(spec.post.phi, spec.post.sigma - h)
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

          SynMoreGoals(Seq(subGoalSpec), kont)
        }
        case Some(h) =>
          assert(false, s"Alloc rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }

  }

  /*
  Free rule: free a block from the pre-state if the post-state is emp

                        Γ ; { φ ; P } ; { ψ ; emp } ---> S
  ------------------------------------------------------------------------------- [free]
   Γ ; { φ ; block(x, n + 1) * x -> (e0 .. en) * P } ; { ψ ; emp } ---> free(x); S
*/
  object FreeRule extends SynthesisRule {

    override def toString: Ident = "[free]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      def isConcreteBlock: Heaplet => Boolean = {
        case Block(v, _) => spec.isConcrete(v)
        case _ => false
      }

      if (post.sigma.isEmp) {
        findHeaplet(isConcreteBlock, spec.pre.sigma) match {
          case None => SynFail
          case Some(h@Block(x, sz)) => {
            val pts = for (off <- 0 until sz) yield {
              findHeaplet(sameLhs(PointsTo(x, off, PConst(0))), spec.pre.sigma) match {
                case Some(pt) => pt
                case None => return SynFail
              }
            }
            val newPre = Assertion(spec.pre.phi, spec.pre.sigma - h - pts)
            val subGoalSpec = Spec(newPre, post, gamma)
            val kont: StmtProducer = stmts => {
              assert(stmts.lengthCompare(1) == 0, s"Free rule expected 1 premise and got ${stmts.length}")
              Free(x, stmts.head)
            }

            SynMoreGoals(Seq(subGoalSpec), kont)
          }
          case Some(h) =>
            assert(false, s"Free rule matched unexpected heaplet ${h.pp}")
            SynFail
        }
      } else SynFail
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
  object FrameRule extends SynthesisRule {

    override def toString: Ident = "[frame]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      // TODO: better side condition: it's okay to remove heaplets with ghosts as long as it doesn't make things unreachable
      // TODO: This is suboptimal: we don't want to check entailment on heaplets, but rather on pre/posts with
      // suitable quantified ghosts/existentials
      def isMatch(hl: Heaplet, hr: Heaplet) = hl.vars.forall(spec.isConcrete) && (hl == hr)
      SynFail

      findMatchingHeaplets(Function.const(true), isMatch, spec.pre.sigma, spec.post.sigma) match {
        case None => SynFail
        case Some((hl, hr)) =>
          val newPre = Assertion(pre.phi, spec.pre.sigma - hl)
          val newPost = Assertion(post.phi, spec.post.sigma - hr)

          val subGoalSpec = Spec(newPre, newPost, gamma)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Frame rule expected 1 premise and got ${stmts.length}")
            stmts.head
          }

          SynMoreGoals(Seq(subGoalSpec), kont)
      }
    }

  }

  /*
  Open rule: unroll a predicate in the pre-state
  TODO: generalize to multiple clauses

              p(params) := { true ? b }
    Γ ; { φ ; b[args/params] * P } ; { ψ ; Q } ---> S
    ---------------------------------------------------- [open]
        Γ ; { φ ; p(args) * P } ; { ψ ; Q } ---> S

   */
  object OpenRule extends SynthesisRule {

    override def toString: Ident = "[open]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      findHeaplet(_.isInstanceOf[SApp], spec.pre.sigma) match {
        case None => SynFail
        case Some(h@SApp(pred,args)) => {
          assert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")
          val InductiveDef(_, params, clauses) = env.predicates (pred)
          assert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val InductiveClause(_, body) = clauses.head
          val actualBody = body.subst((params zip args).toMap)


          val newPre = Assertion(pre.phi, spec.pre.sigma ** actualBody - h)

          val subGoalSpec = Spec(newPre, post, gamma)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Open rule expected 1 premise and got ${stmts.length}")
            stmts.head
          }

          SynMoreGoals(Seq(subGoalSpec), kont)
        }
        case Some(h) =>
          assert(false, s"Open rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }
  }

  /*
  Close rule: unroll a predicate in the post-state
  TODO: generalize to multiple clauses

              p(params) := { true ? b }
    Γ ; { φ ; P } ; { ψ ; b[args/params] * Q } ---> S
    ---------------------------------------------------- [close]
        Γ ; { φ ; P } ; { ψ ; p(args) * Q } ---> S

   */
  object CloseRule extends SynthesisRule {

    override def toString: Ident = "[close]"

    def apply(spec: Spec, env: Environment): SynthesisRuleResult = {
      val Spec(pre, post, gamma: Gamma) = spec

      findHeaplet(_.isInstanceOf[SApp], spec.post.sigma) match {
        case None => SynFail
        case Some(h@SApp(pred, args)) => {
          assert(env.predicates.contains(pred), s"Close rule encountered undefined predicate: $pred")
          val InductiveDef(_, params, clauses) = env.predicates(pred)
          assert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val InductiveClause(_, body) = clauses.head
          val actualBody = body.subst((params zip args).toMap)

          val newPost = Assertion(post.phi, spec.post.sigma ** actualBody - h)

          val subGoalSpec = Spec(pre, newPost, gamma)
          val kont: StmtProducer = stmts => {
            assert(stmts.lengthCompare(1) == 0, s"Close rule expected 1 premise and got ${stmts.length}")
            stmts.head
          }

          SynMoreGoals(Seq(subGoalSpec), kont)
        }
        case Some(h) =>
          assert(false, s"Close rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }
  }

}

