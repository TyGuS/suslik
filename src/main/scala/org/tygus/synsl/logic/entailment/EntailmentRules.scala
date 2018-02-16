package org.tygus.synsl.logic.entailment

import org.tygus.synsl.logic._

/**
  * @author Ilya Sergey
  */

trait EntailmentRules extends LogicUtils {

  /*
    TODO: Unify the definitions below with synthesis machinery,
    as discussed on Feb 13, 2018.
   */
  abstract sealed class EntRuleResult

  case object EntFail extends EntRuleResult

  case class EntMoreGoals(goals: List[Spec]) extends EntRuleResult

  abstract class EntailmentRule {
    def apply(spec: Spec, env: Environment): EntRuleResult
  }

  // ======================================================== //

  /* *********************************************************
   * NORMALIZATION RULES
   * *********************************************************/

  // So far, handling only conjunction with equalities


  /* *********************************************************
   * SUBTRACTION RULES
   * *********************************************************/

  // So far, handling only conjunction with equalities

  /**
    * [AXIOM]
    */
  object Axiom extends EntailmentRule {
    override def toString: String = "[Sub:AXIOM]"
    def apply(spec: Spec, env: Environment): EntRuleResult = {
      val p = simplify(spec.post.phi)
      val s1 = spec.pre.sigma
      val s2 = spec.post.sigma
      if (p == PTrue && s1.isEmp && s2.isEmp) EntMoreGoals(Nil) else EntFail
    }
  }

  /**
    * [=-R]
    */
  object RemoveEq extends EntailmentRule {
    override def toString: String = "[Sub: =-R]"

    def apply(spec: Spec, env: Environment): EntRuleResult = {
      findConjunctAndRest({
        case PEq(x, y) => x == y
        case _ => false
      }, simplify(spec.post.phi)) match {
        case None => EntFail
        case Some((_, rest)) =>
          val newPost = Assertion(mkConjunction(rest), spec.post.sigma)
          val newSpec = Spec(spec.pre, newPost, spec.gamma)
          EntMoreGoals(List(newSpec))
      }
    }
  }

  /**
    * [HYPOTHESIS]
    */
  object Hypothesis extends EntailmentRule {
    override def toString: String = "[Sub: Hypothesis]"
    def apply(spec: Spec, env: Environment): EntRuleResult = {
      (conjuncts(spec.pre.phi), conjuncts(spec.post.phi)) match {
        case (Some(cs1), Some(cs2)) =>
          findCommon((p : PFormula) => true, cs1, cs2) match {
            case Some((p, ps1, ps2)) =>
              val newPost = Assertion(mkConjunction(ps2), spec.post.sigma)
              val newSpec = Spec(spec.pre, newPost, spec.gamma)
              EntMoreGoals(List(newSpec))
            case None => EntFail
          }
        case _ => EntFail
      }
    }
  }

  /**
    * [*-INTRODUCTION]
    */
  object StarIntro extends EntailmentRule {
    override def toString: String = "[Sub: *-Introduction]"
    def apply(spec: Spec, env: Environment): EntRuleResult = {
      val cs1 = spec.pre.sigma.chunks
      val cs2 = spec.pre.sigma.chunks
      findCommon((h : Heaplet) => h.isInstanceOf[PointsTo], cs1, cs2) match {
        case Some((p, ps1, ps2))=>
          val newPre = Assertion(spec.pre.phi, SFormula(ps1))
          val newPost = Assertion(spec.post.phi, SFormula(ps2))
          val newSpec = Spec(newPre, newPost, spec.gamma)
          EntMoreGoals(List(newSpec))
        case None => EntFail
      }
    }
  }

}
