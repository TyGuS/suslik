package org.tygus.suslik.certification

import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.{StmtProducer, SynthesisException}
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, SynthesisRule}

import scala.collection.mutable

object CertTree {
  /**
    * [Certify]: A utility for traversing a successful synthesis result during certification
    * @param nodeId the NodeId of the associated or-node in the synthesis search tree
    * @param goal the current synthesis goal
    * @param kont the continuation that produces the statement for the goal
    * @param rule the synthesis rule that was successfully applied to prove the goal
    */
  case class Node(nodeId: NodeId,
                  goal: Goal,
                  kont: StmtProducer,
                  rule: SynthesisRule) {
    lazy val footprint: Footprint = goal.toFootprint
    val id: Int = hashCode()

    def children: List[Node] = childrenMap.getOrElse(this, List.empty).reverse
    def parent: Option[Node] = parentMap.get(this)

    override def equals(obj: Any): Boolean = obj.isInstanceOf[Node] && (obj.asInstanceOf[Node].nodeId == this.nodeId)
    override def hashCode(): Int = nodeId.hashCode()

    def pp: String = {
      val cs = children

      val builder = new StringBuilder()
      builder.append(s"Node <$id>\n")

      builder.append(s"Goal to solve:\n")

      builder.append(s"${goal.pp}\n")

      builder.append(s"Rule applied: $rule\n")

      builder.append(s"Footprint: $showChildren\n")

      builder.append(s"Parent node: ${parent.map(_.id).getOrElse("none")}\n")
      builder.append(s"Child nodes: [${cs.map(_.id).mkString(", ")}]\n")

      builder.toString()
    }

    def showChildren: String = {
      def showFootprint(f: Footprint): String = s"${f.pre.pp}${f.post.pp}"
      def showDiff(child: Node):String = s"${showFootprint(footprint - child.footprint)} --> ${showFootprint(child.footprint - footprint)}"

      children.length match {
        case 0 => showFootprint(footprint)
        case _ => children.map(showDiff).mkString("; ")
      }
    }
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
    traverse(terminal, e.producer, e.rule, _ => ())
  }

  def addSuccessFromCache(node: OrNode): Unit = {
    for {
      existingNode <- findByGoal(node.goal)
    } yield traverse(node, existingNode.kont, existingNode.rule, _ => ())
  }

  @scala.annotation.tailrec
  private def traverse(on: OrNode, stmtProducer: StmtProducer, rule: SynthesisRule, kont: Node => Unit): Unit = {
    def mkKont(n: Node, prevKont: Node => Unit): Node => Unit = parent => {
      prevKont(n)  // execute the rest of the continuation
      parentMap(n) = parent  // add link: child -> parent
      childrenMap(parent) =  // add link: parent -> child
        n :: childrenMap.getOrElse(parent, List.empty)
    }

    val n = Node(on.id, on.goal, stmtProducer, rule)
    on.parent match {
      case Some(parentAn) if !parentMap.contains(n) =>  // only continue if parent hasn't been added before
        traverse(parentAn.parent, parentAn.kont, parentAn.rule, mkKont(n, kont))
      case _ =>
        kont(n)
    }
  }

  private def findByGoal(goal: Goal): Option[Node] =
    parentMap.keySet.find(n => n.goal.pre == goal.pre && n.goal.post == goal.post)

  def get(id: NodeId): Option[Node] =
    childrenMap.keySet.find(_ == Node(id, null, null, null))

  def clear(): Unit = {
    childrenMap.clear
    parentMap.clear
  }

  // Pretty prints the tree rooted at a node (tries the root node by default)
  def pp(id: NodeId = Vector()): String = {
    def visit(n: Node): String = {
      val builder = new StringBuilder()
      builder.append(n.pp)
      builder.append("\n")
      for (child <- n.children)
        builder.append(visit(child))
      builder.toString()
    }

    val n = get(id).getOrElse(throw SynthesisException(s"No node found matching id $id"))
    visit(n)
  }
}
