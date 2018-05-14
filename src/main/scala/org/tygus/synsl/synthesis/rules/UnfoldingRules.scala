package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.language.Statements.If
import org.tygus.synsl.language.{Ident, VoidType}
import org.tygus.synsl.logic._
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
        ctail.foldLeft(finalBranch){case (eb, (c, tb)) => If(c, tb, eb)}
      }
    }

    /**
      * TODO: Handle multiple predicate application occurrences, i.e., provide multiple sets of sub-goals
      * TODO: This can lead to multiple induction hypotheses, all delivered by the same rule
      */
    private def mkInductiveSubGoals(goal: Goal, env: Environment): Option[Seq[(PFormula, Goal)]] = {
      val Goal(pre, post, gamma) = goal
      findHeaplet(_.isInstanceOf[SApp], pre.sigma) match {
        case Some(h@SApp(pred, args, tag)) if tag == 0 =>
          // Only 0-tagged (i.e., not yet once unfolded predicates) can be unfolded
          ruleAssert(env.predicates.contains(pred), s"Open rule encountered undefined predicate: $pred")
          val InductivePredicate(_, params, clauses) = env.predicates(pred)
          val sbst = params.zip(args).toMap
          val remainingChunks = pre.sigma.chunks.filter(_ != h)
          val newGoals = for {
            InductiveClause(_sel, _body) <- clauses
            sel = _sel.subst(sbst)
            body = _body.subst(sbst)
            newPrePhi = mkConjunction(sel :: conjuncts(pre.phi))
            newPreSigma = SFormula(body.chunks ++ remainingChunks).bumpUpSAppTag
          } yield (sel, goal.copy(pre = Assertion(newPrePhi, newPreSigma)))
          Some(newGoals)
        case _ => None
      }
    }

    private def mkIndHyp(goal: Goal, env: Environment): Environment = {
      val fname = Var("frec").refresh(env.functions.keySet.map(Var)).name
      // TODO: provide a proper type, not VOID
      val fspec = FunSpec(fname, VoidType, goal.gamma, goal.pre, goal.post)
      env.copy(functions = env.functions + (fname -> fspec))
    }

    def apply(goal: Goal, env: Environment): SynthesisRuleResult = {
      mkInductiveSubGoals(goal, env) match {
        case None => SynFail
        case Some(selGoals) =>
          val (selectors, subGoals) = selGoals.unzip
          val newEnv = mkIndHyp(goal, env)
          val goalsWithNewEnv = subGoals.map(g => (g, newEnv))
          SynAndGoals(goalsWithNewEnv, kont(selectors))
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
        case Some(h@SApp(pred, args, _)) =>
          ruleAssert(env.predicates.contains(pred), s"Close rule encountered undefined predicate: $pred")
          val InductivePredicate(_, params, clauses) = env.predicates(pred)

          //ruleAssert(clauses.lengthCompare(1) == 0, s"Predicates with multiple clauses not supported yet: $pred")
          val substMap = params.zip(args).toMap
          val subGoalEnvs = for (InductiveClause(selector, body) <- clauses) yield {
            val actualBody = body.subst(substMap)
            val actualSelector = selector.subst(substMap)
            val newPhi = simplify(mkConjunction(List(actualSelector, post.phi)))
            val newPost = Assertion(newPhi, goal.post.sigma ** actualBody - h)
            (Goal(pre, newPost, gamma), env)
          }
          SynOrGoals(subGoalEnvs, kont)
        case Some(h) =>
          ruleAssert(false, s"Close rule matched unexpected heaplet ${h.pp}")
          SynFail
      }
    }
  }

}
