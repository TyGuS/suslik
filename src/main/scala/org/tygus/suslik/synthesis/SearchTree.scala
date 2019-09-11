package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Solution
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.rules.Rules.StmtProducer

/**
  * And-or tree that represents the space of all possible derivations
  */
object SearchTree {

  type NodeId = Vector[Int]

  case class OrNode(id: NodeId, goal: Goal, parent: Option[AndNode]) {
    // Does this node have a ancestor with label l?
    def hasAncestor(l: Vector[Int]): Boolean =
      if (id == l) true
      else if (id.length < l.length) false
      else parent match {
        // this node cannot be the root, because label.lengh > l.length
        case Some(p) => p.hasAncestor(l)
        case None => throw SynthesisException("OrNode cannot be root")
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
    def fail(wl: List[OrNode]): List[OrNode] = parent match {
      case None => wl // this is the root; wl must already be empty
      case Some(an) => { // a subgoal has failed
        val newWL = wl.filterNot(_.hasAncestor(an.id)) // prune all other descendants of an
        if (newWL.exists(_.hasAncestor(an.parent.id))) { // does my grandparent have other open alternatives?
          newWL
        } else {
          an.parent.fail(newWL)
        }
      }
    }

    // This node has succeeded: update worklist or return solution
    def succeed(s: Solution, wl: List[OrNode]): Either[List[OrNode], Solution] = parent match {
      case None => Right(s) // this is the root: synthesis succeeded
      case Some(an) => { // a subgoal has succeeded
        val newWL = wl.filterNot(_.hasAncestor(id)) // prune all my descendants from worklist
        // Check if an has more open subgoals:
        if (an.kont.arity == 1) { // there are no more open subgoals: an has succeeded
          an.parent.succeed(an.kont(List(s)), newWL)
        } else { // there are other open subgoals: partially apply and replace in descendants
          val newAN = an.copy(kont = an.kont.partApply(s))
          Left(newWL.map(_.replaceAncestor(an.id, newAN)))
        }
      }
    }

    def depth: Int = parent match {
      case None => 0
      case Some(p) => p.parent.depth + 1
    }

    def pp(d: Int = 0): String = parent match {
      case None => "-"
      case Some(p) =>
        if (d > 2) s"...($depth)"
        else {
          val subgoalID = if (id.head < 0) "" else s".${id.head.toString}"
          p.pp(d + 1) ++ subgoalID
        }
    }
  }

  case class AndNode(id: NodeId, kont: StmtProducer, parent: OrNode, ruleLabel: String) {
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
      parentPP ++ ruleLabel
    }
  }
}
