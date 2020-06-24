package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Solution
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import org.tygus.suslik.util.SynStats

/**
  * And-or tree that represents the space of all possible derivations
  */
object SearchTree {

  // Node's position in the search tree
  // (index of each reflexive ancestor among its siblings; youngest to oldest)
  type NodeId = Vector[Int]

  type Worklist = List[OrNode]

  // List of nodes to process
  var worklist: Worklist = List()

  // Initialize worklist: root or-node containing the top-level goal
  def init(initialGoal: Goal): Unit = {
    val root = OrNode(Vector(), initialGoal, None)
    worklist = List(root)
  }

  /**
    * Or-node in the search tree;
    * represents a synthesis goal to solve.
    * For this node to succeed, one of its children has to succeed.
    */
  case class OrNode(id: NodeId, goal: Goal, parent: Option[AndNode]) {
    // My index among the children of parent
    def childIndex: Int = id.headOption.getOrElse(0).max(0)

    // Does this node have a ancestor with label l?
    def hasAncestor(l: Vector[Int]): Boolean =
      if (id == l) true
      else if (id.length < l.length) false
      else parent match {
        // this node cannot be the root, because label.lengh > l.length
        case Some(p) => p.hasAncestor(l)
        case _ => false
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
    def fail(implicit stats: SynStats, config: SynConfig): Unit = {
      memo.save(goal, Failed)
      parent match {
        case None => assert(worklist.isEmpty)// this is the root; wl must already be empty
        case Some(an) => { // a subgoal has failed
          stats.addFailedNode(an)
          worklist = pruneDescendants(an.id, worklist)  // prune all other descendants of an
          if (!worklist.exists(_.hasAncestor(an.parent.id))) { // does my grandparent have other open alternatives?
            an.parent.fail
          }
        }
      }
    }

    // This node has succeeded: update worklist or return solution
    def succeed(s: Solution)(implicit config: SynConfig): Option[Solution] = {
      memo.save(goal, Succeeded(s))
      parent match {
        case None => Some(s) // this is the root: synthesis succeeded
        case Some(an) => { // a subgoal has succeeded
          worklist = pruneDescendants(id, worklist) // prune all my descendants from worklist
          // Check if an has more open subgoals:
          if (an.kont.arity == 1) { // there are no more open subgoals: an has succeeded
            an.parent.succeed(an.kont(List(s)))
          } else { // there are other open subgoals: partially apply and replace in descendants
            val newAN = an.copy(kont = an.kont.partApply(s))
            worklist = worklist.map(_.replaceAncestor(an.id, newAN))
            None
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

    def pp(d: Int = 0): String = parent match {
      case None => "-"
      case Some(p) =>
        if (d > 2) s"...($depth)"
        else {
          val subgoalID = if (id.head < 0) "" else s".${id.head}"
          p.pp(d + 1) ++ subgoalID
        }
    }

    lazy val cost: Int = {
//      val history = ruleHistory
//      val callCount = history.count(_ == CallRule)
//      val hasAbduceCall = history.nonEmpty && history.head == AbduceCall
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
  case class AndNode(id: NodeId, kont: StmtProducer, parent: OrNode, rule: SynthesisRule) {
    // Does this node have an ancestor with label l?
    def hasAncestor(l: NodeId): Boolean =
      if (id == l) true
      else if (id.length < l.length) false
      else parent.hasAncestor(l)

    def pp(d: Int = 0): String = {
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
