package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Solution
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.rules.Rules.{InvertibleRule, StmtProducer, SynthesisRule}
import org.tygus.suslik.util.SynStats

import scala.collection.mutable

/**
  * And-or tree that represents the space of all possible derivations
  */
object SearchTree {

  // Node's position in the search tree
  // (index of each reflexive ancestor among its siblings; youngest to oldest)
  type NodeId = Vector[Int]

  // For each or-node, transitions that have been tried before and failed;
  // i.e. transitions of its older siblings
  type PrecursorMap = mutable.Map[NodeId, Set[Transition]]

  /**
    * Or-node in the search tree;
    * represents a synthesis goal to solve.
    * For this node to succeed, one of its children has to succeed.
    */
  case class OrNode(id: NodeId, goal: Goal, parent: Option[AndNode], produce: Footprint) {
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
        else p.parent.replaceAncestor(l, n)
    }

    // This node has failed: prune siblings from worklist
    def fail(wl: List[OrNode])(implicit precursors: PrecursorMap, stats: SynStats): List[OrNode] = parent match {
        case None => wl // this is the root; wl must already be empty
        case Some(an) => { // a subgoal has failed
          stats.addFailedNode(an)
          val newWL = wl.filterNot(_.hasAncestor(an.id)) // prune all other descendants of an
          precursors.retain((i, _) => !i.endsWith(an.id)) // also prune them from precursor map
          if (newWL.exists(_.hasAncestor(an.parent.id))) { // does my grandparent have other open alternatives?
            newWL
          } else {
            an.parent.fail(newWL)
          }
        }
      }

    // This node has succeeded: update worklist or return solution
    def succeed(s: Solution, wl: List[OrNode])(implicit precursors: PrecursorMap): Either[List[OrNode], Solution] = parent match {
      case None => Right(s) // this is the root: synthesis succeeded
      case Some(an) => { // a subgoal has succeeded
        val newWL = wl.filterNot(_.hasAncestor(id)) // prune all my descendants from worklist
        precursors.retain((i, _) => !i.endsWith(this.id)) // also prune them from precursor map
        // Check if an has more open subgoals:
        if (an.kont.arity == 1) { // there are no more open subgoals: an has succeeded
          an.parent.succeed(an.kont(List(s)), newWL)
        } else { // there are other open subgoals: partially apply and replace in descendants
          val newAN = an.copy(kont = an.kont.partApply(s))
          Left(newWL.map(_.replaceAncestor(an.id, newAN)))
        }
      }
    }

    // Or-nodes that are proper ancestors of this nodes in the search tree
    def ancestors: List[OrNode] = parent match {
      case None => Nil
      case Some(p) => {
        val gp = p.parent
        gp :: gp.ancestors
      }
    }

    // Number of proper ancestors
    def depth: Int = ancestors.length

    def isInvertible: Boolean = parent match {
      case None => false
      case Some(p) => p.rule.isInstanceOf[InvertibleRule]
    }

    // Transition that describes the relationship between this node's goal
    // and its closest ancestor's goal
    def transition: Transition = Transition(parent.map(_.consume).getOrElse(emptyFootprint), produce)

    // All (reflexive) ancestors of this node that commute with a transition that consumes newConsume,
    // i.e. could be placed after this new transition without affecting the resulting goal
    def commuters(newTransition: Transition): List[OrNode] =
      (this :: ancestors).filterNot(_.isInvertible).takeWhile(n =>
        n.transition.consume.disjoint(newTransition.removed) // the new transition doesn't remove something an ancestor depends on
          && n.transition.produce.disjoint(newTransition.consume)) // the new transition doesn't rely on something produced by the ancestor

    def pp(d: Int = 0): String = parent match {
      case None => "-"
      case Some(p) =>
        if (d > 2) s"...($depth)"
        else {
          val subgoalID = if (id.head < 0) "" else s".${id.head.toString}"
          p.pp(d + 1) ++ subgoalID
        }
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
