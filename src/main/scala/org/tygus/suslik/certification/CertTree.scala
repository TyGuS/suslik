package org.tygus.suslik.certification

import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, StmtProducer, SynthesisRule}

import scala.collection.mutable

object Tree {

  /**
    * [Certify]: A utility for traversing a successful synthesis result during certification
    * @param id the NodeId of the associated or-node in the synthesis search tree
    * @param goal the current synthesis goal
    * @param kont the continuation that produces the statement for the goal
    * @param rule the synthesis rule that was successfully applied to prove the goal
    * @param produce the `produce` footprint of the associated or-node
    * @param consume the `consume` footprint of the associated and-node
    */
  case class Node(id: NodeId,
                  goal: Goal,
                  kont: StmtProducer,
                  rule: SynthesisRule,
                  produce: Footprint,
                  consume: Footprint) {
    def children: List[Node] = childrenMap.getOrElse(this, List.empty).reverse
    def parent: Option[Node] = parentMap.get(this)

    override def equals(obj: Any): Boolean = obj.isInstanceOf[Node] && (obj.asInstanceOf[Node].id == this.id)
    override def hashCode(): Int = id.hashCode()
  }

  // [Certify]: Maintain a certification tree as a pair of bidirectional hash maps
  private val childrenMap: mutable.Map[Node, List[Node]] = mutable.Map.empty
  private val parentMap: mutable.Map[Node, Node] = mutable.Map.empty
  def root: Option[Node] = get(Vector())

  /**
    * [Certify]: Adds a successful terminal or-node and its ancestors
    * from the synthesis search tree to this certification tree
    * @param terminal a terminal or-node in the search tree
    * @param e a successful rule expansion for the terminal or-node
    */
  def addSuccessfulPath(terminal: OrNode, e: RuleResult): Unit = {
    def mkKont(n: Node, prevKont: Node => Unit): Node => Unit = parent => {
      prevKont(n)  // execute the rest of the continuation
      parentMap(n) = parent  // add link: child -> parent
      childrenMap(parent) =  // add link: parent -> child
        n :: childrenMap.getOrElse(parent, List.empty)
    }

    @scala.annotation.tailrec
    def traverse(an: AndNode, kont: Node => Unit): Unit = {
      val on = an.parent
      val n = Node(on.id, on.goal, an.kont, an.rule, on.produce, an.consume)
      on.parent match {
        case Some(parentAn) if !parentMap.contains(n) =>  // only continue if parent hasn't been added before
          traverse(parentAn, mkKont(n, kont))
        case _ =>
          kont(n)
      }
    }

    val terminalAn = AndNode(Vector(), e.kont, terminal, e.consume, e.rule)
    traverse(terminalAn, _ => ())
  }

  def get(id: NodeId): Option[Node] = childrenMap.keySet.find(_ == Node(id, null, null, null, null, null))

  def clear(): Unit = {
    childrenMap.clear
    parentMap.clear
  }
}
