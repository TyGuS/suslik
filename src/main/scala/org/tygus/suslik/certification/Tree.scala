package org.tygus.suslik.certification

import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId}
import org.tygus.suslik.synthesis.rules.Rules.{StmtProducer, SynthesisRule}

import scala.collection.mutable

object Tree {

  /**
    * A utility for traversing a successful synthesis result during certification
    * @param id the NodeId of the associated or-node in the synthesis search tree
    * @param parent the parent node
    * @param goal the current synthesis goal
    * @param kont the continuation that produces the statement for the goal
    * @param rule the synthesis rule that was successfully applied to prove the goal
    * @param produce the `produce` footprint of the associated or-node
    * @param consume the `consume` footprint of the associated and-node
    */
  case class Node(id: NodeId, // the id of the associated or-node
                  parent: Option[Node],
                  goal: Goal,
                  kont: StmtProducer,
                  rule: SynthesisRule,
                  produce: Footprint,
                  consume: Footprint) {
    def children: List[Node] = m.getOrElse(this, List.empty).reverse

    override def equals(obj: Any): Boolean = obj.isInstanceOf[Node] && (obj.asInstanceOf[Node].id == this.id)
    override def hashCode(): Int = id.hashCode()
  }

  object Node {
    def fromSynthesis(an: AndNode): Node = {
      val on = an.parent
      val parent =
        on.parent.map(parentAn =>
          // Search locally first, and recursively create one if not found
          get(parentAn.parent.id).getOrElse(fromSynthesis(parentAn)))
      Node(
        on.id,
        parent,
        on.goal,
        an.kont,
        an.rule,
        on.produce,
        an.consume
      )
    }
  }

  private val m: mutable.Map[Node, List[Node]] = mutable.Map.empty
  def root: Option[Node] = get(Vector())

  @scala.annotation.tailrec
  def add(node: Node): Unit = node.parent match {
    case Some(parent) =>
      m.get(parent) match {
        case Some(children) =>
          if (!children.contains(node)) m(parent) = node :: children
        case None =>
          m(parent) = List(node)
      }
      add(parent)
    case None => // no-op
  }

  def get(id: NodeId): Option[Node] = m.keySet.find(_ == Node(id, None, null, null, null, null, null))

  def clear(): Unit = m.clear
}
