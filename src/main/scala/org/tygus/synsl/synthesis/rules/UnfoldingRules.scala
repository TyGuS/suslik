package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Ident
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis._

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

object UnfoldingRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-unfolding"

  /*
  Open rule: unroll a predicate in the pre-state
  TODO: generalize to multiple clauses

              p(params) := { true ? b }
    Γ ; { φ ; b[args/params] * P } ; { ψ ; Q } ---> S
    ---------------------------------------------------- [open]
        Γ ; { φ ; p(args) * P } ; { ψ ; Q } ---> S

   */
  object OpenRule extends SynthesisRule {

    override def toString: Ident = "[Unfold: open]"

    private val kont: StmtProducer = stmts => {
      ruleAssert(stmts.lengthCompare(1) == 0, s"Open rule expected 1 premise and got ${stmts.length}")
      stmts.head
    }

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      val Goal(pre, post, gamma: Gamma) = goal

      findHeaplet(_.isInstanceOf[SApp], goal.pre.sigma) match {
        case None => SynFail
        case Some(h@SApp(pred, args)) =>
          ruleAssert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")
          val InductivePredicate(_, params, clauses) = env.predicates(pred)
          ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val InductiveClause(_, body) = clauses.head
          val actualBody = body.subst((params zip args).toMap)
          val newPre = Assertion(pre.phi, goal.pre.sigma ** actualBody - h)
          val subGoal = Goal(newPre, post, gamma)
          SynAndGoals(Seq(subGoal), kont)
        case Some(h) =>
          ruleAssert(false, s"Open rule matched unexpected heaplet ${h.pp}")
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

    override def toString: Ident = "[Unfold: close]"

    private val kont: StmtProducer = stmts => {
      ruleAssert(stmts.lengthCompare(1) == 0, s"Close rule expected 1 premise and got ${stmts.length}")
      stmts.head
    }

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      val Goal(pre, post, gamma: Gamma) = goal

      findHeaplet(_.isInstanceOf[SApp], goal.post.sigma) match {
        case None => SynFail
        case Some(h@SApp(pred, args)) =>
          ruleAssert(env.predicates.contains(pred), s"Close rule encountered undefined predicate: $pred")
          val InductivePredicate(_, params, clauses) = env.predicates(pred)

          //ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val substMap = params.zip(args).toMap
          val subGoals = for (InductiveClause(selector, body) <- clauses) yield {
            val actualBody = body.subst(substMap)
            val actualSelector = selector.subst(substMap)
            val newPhi = simplify(mkConjunction(List(actualSelector, post.phi)))
            val newPost = Assertion(newPhi, goal.post.sigma ** actualBody - h)
            Goal(pre, newPost, gamma)
          }
          SynOrGoals(subGoals, kont)
        case Some(h) =>
          ruleAssert(false, s"Close rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }
  }

}
