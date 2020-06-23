package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.{CardType, PrettyPrinting}
import org.tygus.suslik.language.Expressions.{BinaryExpr, OpLt, Var}
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.StmtProducer

object Rules {

  // Pair of cardinality variables
  type TracePair = (Var, Var)

  /**
    * Which pairs of cardinality variables strictly decrease (progressing) vs non-strictly decrease (non-progressing)
    * between a goal and a subgoal
    */
  case class Transition(progressing: List[TracePair], nonProgressing: List[TracePair]) extends PrettyPrinting {
    private def showTracePairs(pairs: List[TracePair]): String = pairs.map { case (v1, v2) => s"(${v1.pp}, ${v2.pp})"}.mkString(", ")
    override def pp : String = s"{${showTracePairs(progressing)}}, {${showTracePairs(nonProgressing)}}"
  }

  object Transition {
    // Default transition between a goal and subgoal:
    // assumes the variable names have the same meaning between the two goals.
    // This should not be used for backlinks.
    def apply(goal: Goal, subgoal: Goal): Transition = {
      // TODO: beef up with SMT reasoning if we want to support different card constraints
      val strictInequalities = for {
        BinaryExpr(OpLt, v1@Var(_), v2@Var(_)) <- subgoal.pre.phi.conjuncts.toList
        if v1.getType(subgoal.gamma).contains(CardType)
        if v2.getType(subgoal.gamma).contains(CardType)
        if goal.pre.vars.contains(v2)
      } yield (v2, v1)
      val sharedCardVars = for {
        v <- subgoal.vars.toList
        if v.getType(subgoal.gamma).contains(CardType)
        if goal.pre.vars.contains(v)
      } yield (v, v)
      new Transition(strictInequalities, sharedCardVars)
    }
  }
  
  /**
    * Result of a rule application:
    * sub-goals to be solved and
    * a statement producer that assembles the sub-goal results
    */
  case class RuleResult(subgoals: Seq[Goal],
                        producer: StmtProducer,
                        rule: SynthesisRule,
                        transitions: Seq[Transition])

  object RuleResult {
    def apply(subgoals: Seq[Goal], producer: StmtProducer, rule: SynthesisRule, goal: Goal) =
      new RuleResult(subgoals, producer, rule, subgoals.map(sub => Transition(goal, sub)))
  }


  /**
    * A generic class for a deductive rule to be applied
    *
    * @author Ilya Sergey
    */
  abstract class SynthesisRule extends PureLogicUtils {
    // Apply the rule and get all possible sub-derivations
    def apply(goal: Goal): Seq[RuleResult]
  }

  /**
    * Different kinds of rules
    */

  // Invertible rule: does not restrict the set of derivations,
  // so no need to backtrack in case of failure
  trait InvertibleRule

  // This rule produces code
  trait GeneratesCode

  trait UnfoldingPhase {
    def heapletFilter(h: Heaplet): Boolean = {
      h.isInstanceOf[SApp]
    }
  }

  trait BlockPhase {
    def heapletFilter(h: Heaplet): Boolean = {
      h.isInstanceOf[Block]
    }
  }

  trait FlatPhase {
    def heapletFilter(h: Heaplet): Boolean = true
  }


  def nubBy[A,B](l:List[A], p:A=>B):List[A] =
  {
    def go[A,B](l:List[A], p:A=>B, s:Set[B], acc:List[A]):List[A] = l match
    {
      case Nil => acc.reverse
      case x::xs if s.contains(p(x)) => go(xs,p,s,acc)
      case x::xs                     => go(xs,p,s+p(x),x::acc)
    }
    go(l,p,Set.empty,Nil)
  }
}
