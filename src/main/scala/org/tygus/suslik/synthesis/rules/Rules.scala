package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.StmtProducer

object Rules {
  
  /**
    * Result of a rule application:
    * sub-goals to be solved and
    * a statement producer that assembles the sub-goal results
    */
  case class RuleResult(subgoals: Seq[Goal], producer: StmtProducer, consume: Footprint, rule: SynthesisRule)
    extends PrettyPrinting with PureLogicUtils {

    override def pp: String = rule.toString // s"[${subgoals.map(_.label.pp).mkString(", ")}]"

    def produces(parent: Goal): Seq[Footprint] = subgoals.map(g => g.allHeaplets - (parent.allHeaplets - consume))
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
