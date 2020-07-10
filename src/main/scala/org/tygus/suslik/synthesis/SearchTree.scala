package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Solution
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.Termination.Transition
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, SynthesisRule}
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

  // List of leaf nodes that succeeded
  var successLeaves: Worklist = List()

  // Initialize worklist: root or-node containing the top-level goal
  def init(initialGoal: Goal): Unit = {
    val root = OrNode(Vector(), initialGoal, None)
    worklist = List(root)
    successLeaves = List()
  }

  /**
    * Or-node in the search tree;
    * represents a synthesis goal to solve.
    * For this node to succeed, one of its children has to succeed.
    */
  case class OrNode(id: NodeId, goal: Goal, parent: Option[AndNode], extraCost: Int = 0) {
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
          successLeaves = pruneDescendants(an.id, successLeaves) // also from the list of succeeded leaves
          if (!worklist.exists(_.hasAncestor(an.parent.id))) { // does my grandparent have other open alternatives?
            an.parent.fail
          }
        }
      }
    }

    // This node has succeeded: update worklist or return solution
    def succeed(s: Solution)(implicit config: SynConfig): Option[Solution] = {
      memo.save(goal, Succeeded(s))
      successLeaves = successLeaves.filterNot(n => this.isFailedDescendant(n))  // prune members of partially successful branches
      parent match {
        case None => Some(s) // this is the root: synthesis succeeded
        case Some(an) => { // a subgoal has succeeded
          worklist = pruneDescendants(id, worklist) // prune all my descendants from worklist
          val newAN = an.copy(kont = an.kont.partApply(s)) // record solution in my parent
          worklist = worklist.map(_.replaceAncestor(an.id, newAN)) // replace my parent in the tree
          successLeaves = successLeaves.map(_.replaceAncestor(an.id, newAN))
          // Check if my parent has more open subgoals:
          if (newAN.kont.arity == 0) { // there are no more open subgoals: an has succeeded
            newAN.parent.succeed(newAN.kont(List()))
          } else { // there are other open subgoals:
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

    // Is n part of a branch of my descendants that hasn't yet fully succeeded?
    // Yes if there's a incomplete and-node on the way from n to me
    private def isFailedDescendant(n: OrNode): Boolean =
      n.andAncestors.find(an => an.kont.arity > 0) match {
      case None => false
      case Some(an) => an.hasAncestor(this.id)
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

    // Is other from the same branch of the search as myself?
    private def isAndSibling(other: OrNode): Boolean = {
      val leastCommonAndAncestor = andAncestors.find(an => other.andAncestors.contains(an))
      leastCommonAndAncestor match {
        case None => false // this can happen if the only common ancestor is root
        case Some(lcan) => {
          val lcon = ancestors.find(on => other.ancestors.contains(on)).get
          // Since these are least common ancestors, one must be the parent of the other
          assert(lcon.parent.contains(lcan) || lcan.parent == lcon)
          // we are and-siblings if our least common and-ancestor is below our least common or-ancestor:
          lcan.parent == lcon
        }
      }
    }

    // The partial derivation that this node is part of (represented as a subset of success leaves)
    def partialDerivation: List[OrNode] = successLeaves.filter(isAndSibling)

    // All alternative partial derivations that this node is participating in
    // (each partial derivation is represented as a subset of success leaves)
    // this is needed when and-siblings are not necessarily suspended, e.g. when memo is off
    def allPartialDerivations: List[List[OrNode]] = {
      // These nodes are in the same branch as me, but not necessarily with each other
      val relevantNodes = successLeaves.filter(isAndSibling)

      // Are all nodes in s pairwise and-siblings?
      def allAndSiblings(s: Set[OrNode]): Boolean = {
        val results: Set[Boolean] = for { x <- s ; y <- s - x} yield x.isAndSibling(y)
        results.forall(x => x)
      }

      val candidateDerivations = relevantNodes.toSet.subsets.filter(allAndSiblings).toList
      assert(candidateDerivations.nonEmpty, "Candidate derivations should not be empty")
      val maximalDerivations = for {
        d <- candidateDerivations
        // Only keep d if it's maximal, i.e. there is no candidate derivation that is a strict superset of d
        if candidateDerivations.forall(c => c == d || !d.subsetOf(c))
      } yield d.toList
      assert(maximalDerivations.nonEmpty)
      maximalDerivations
    }

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
      goal.cost.max(extraCost)
    }

    override def equals(obj: Any): Boolean = obj.isInstanceOf[OrNode] && (obj.asInstanceOf[OrNode].id == this.id)
    override def hashCode(): Int = id.hashCode()
  }

  /**
    * And-node in the search tree;
    * represents a set of premises of a rule application, whose result should be combined with kont.
    * For this node to succeed, all of its children (premises, subgoals) have to succeed.
    */
  case class AndNode(id: NodeId, parent: OrNode, kont: StmtProducer, rule: SynthesisRule, transitions: Seq[Transition]) {
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

  object AndNode {
    def apply(id: NodeId, parent: OrNode, result: RuleResult): AndNode =
      new AndNode(id, parent, result.producer, result.rule, result.transitions)
  }

}
