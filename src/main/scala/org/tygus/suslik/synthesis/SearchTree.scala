package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Solution
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.rules.Rules.{InvertibleRule, StmtProducer, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules.{AbduceCall, CallRule}
import org.tygus.suslik.util.SynStats

/**
  * And-or tree that represents the space of all possible derivations
  */
object SearchTree {

  // Node's position in the search tree
  // (index of each reflexive ancestor among its siblings; youngest to oldest)
  type NodeId = Vector[Int]

  /**
    * Or-node in the search tree;
    * represents a synthesis goal to solve.
    * For this node to succeed, one of its children has to succeed.
    */
  case class OrNode(id: NodeId, goal: Goal, parent: Option[AndNode], produce: Footprint) {
    // My index among the children of parent
    def childIndex: Int = id.headOption.getOrElse(0).max(0)

    // Does this node have a ancestor with label l?
    def hasAncestor(l: Vector[Int]): Boolean =
      if (id == l) true
      else if (id.length < l.length) false
      else parent match {
        // this node cannot be the root, because label.lengh > l.length
        case Some(p) => p.hasAncestor(l)
      }

    // Replace the ancestor labeled l with newAN
    def replaceAncestor(l: NodeId, n: AndNode): OrNode = parent match {
      case None => this
      case Some(p) =>
        if (p.id == l) copy(parent = Some(n))
        else if (p.id.length <= l.length) this
        else copy(parent = Some(p.copy(parent = p.parent.replaceAncestor(l, n))))
    }

    // This node has failed: prune siblings from worklist
    def fail(wl: List[OrNode])(implicit stats: SynStats, config: SynConfig): List[OrNode] = {
      memo.save(goal, Failed())
      parent match {
        case None => wl // this is the root; wl must already be empty
        case Some(an) => { // a subgoal has failed
          stats.addFailedNode(an)
          val newWL = pruneDescendants(an.id, wl)  // prune all other descendants of an
          if (newWL.exists(_.hasAncestor(an.parent.id))) { // does my grandparent have other open alternatives?
            newWL
          } else {
            an.parent.fail(newWL)
          }
        }
      }
    }

    // This node has succeeded: update worklist or return solution
    def succeed(s: Solution, wl: List[OrNode])(implicit config: SynConfig): Either[List[OrNode], Solution] = {
      memo.save(goal, Succeeded(s))
      parent match {
        case None => Right(s) // this is the root: synthesis succeeded
        case Some(an) => { // a subgoal has succeeded
          val newWL = pruneDescendants(id, wl) // prune all my descendants from worklist
          // Check if an has more open subgoals:
          if (an.kont.arity == 1) { // there are no more open subgoals: an has succeeded
            an.parent.succeed(an.kont(List(s)), newWL)
          } else { // there are other open subgoals: partially apply and replace in descendants
            val newAN = an.copy(kont = an.kont.partApply(s, childIndex))
            Left(newWL.map(_.replaceAncestor(an.id, newAN)))
          }
        }
      }
    }

    // Worklist `wl` with all descendants of `ancestor` pruned
    private def pruneDescendants(ancestor: NodeId, wl: List[OrNode]): List[OrNode] = {
      val (toForget, newWL) = wl.partition(_.hasAncestor(ancestor))
      toForget.foreach(_.forget(ancestor))
      newWL
    }

    // Remove reflexive ancestors of this node until `until` from memo
    private def forget(until: NodeId): Unit = parent match {
      case None =>
      case Some(an) => if (an.id.length >= until.length) {
        memo.forgetExpanded(this.goal)
        an.parent.forget(until)
      }
    }

    // And nodes that are proper ancestors of this node in the search tree
    def andAncestors: List[AndNode] = parent match {
      case None => Nil
      case Some(p) => p :: p.parent.andAncestors
    }

    // Or-nodes that are proper ancestors of this node in the search tree
    def ancestors: List[OrNode] = andAncestors.map(_.parent)

    // Rules that lead to this node
    def ruleHistory: List[SynthesisRule] = andAncestors.map(_.rule)

    // Number of proper ancestors
    def depth: Int = ancestors.length

    // Transition that describes the relationship between this node's goal
    // and its closest ancestor's goal
    def transition: Transition = Transition(parent.map(_.consume).getOrElse(emptyFootprint), produce)

    def pp(d: Int = 0): String = parent match {
      case None => "-"
      case Some(p) =>
        if (d > 2) s"...($depth)"
        else {
          val subgoalID = if (id.head < 0) "" else s".${id.head.toString}"
          p.pp(d + 1) ++ subgoalID
        }
    }

    lazy val cost: Int = {
//      val history = ruleHistory
//      val callCount = history.count(_ == CallRule)
//      val hasAbduceCall = history.nonEmpty && history.head == AbduceCall
      // TODO: we'll need to include calls in the cost if we don't lock tags
      goal.cost  // (callCount + (if (hasAbduceCall) 1 else 0))
    }

    override def equals(obj: Any): Boolean = obj.isInstanceOf[OrNode] && (obj.asInstanceOf[OrNode].id == this.id)
    override def hashCode(): Int = id.hashCode()
  }

  /**
    * And-node in the search tree;
    * represents a set of premises of a rule application, whose result should be combined with kont.
    * For this node to succeed, all of its children (premises, subgoals) have to succeed.
    */
  case class AndNode(id: NodeId, kont: StmtProducer, parent: OrNode, consume: Footprint, rule: SynthesisRule) {
    // Does this node have an ancestor with label l?
    def hasAncestor(l: NodeId): Boolean =
      if (id == l) true
      else if (id.length < l.length) false
      else parent.hasAncestor(l)

    def pp(d: Int): String = {
      val parentPP = parent.parent match {
        case None => ""
        case Some(_) => s"${parent.pp(d)}-"
      }
      parentPP ++ rule.toString
    }

    override def equals(obj: Any): Boolean = obj.isInstanceOf[AndNode] && (obj.asInstanceOf[AndNode].id == this.id)
    override def hashCode(): Int = id.hashCode()
  }

}
