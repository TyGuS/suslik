package org.tygus.suslik.certification

import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.report.ProofTraceCert
import org.tygus.suslik.synthesis.SearchTree.{NodeId, OrNode}
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule

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

    def children: Seq[Node] = childrenMap.getOrElse(this, Seq.empty)
    def parent: Option[Node] = parentMap.get(this)

    def ppId: String = s"<${nodeId.mkString(",")}>"

    def pp: String = {
      val cs = children

      val builder = new StringBuilder()
      builder.append(s"Node $ppId\n")
      builder.append(s"Goal to solve:\n")
      builder.append(s"${goal.pp}\n")
      builder.append(s"Rule applied: $rule\n")
      builder.append(s"Footprint: $showChildren\n")
      builder.append(s"Parent node: ${parent.map(_.ppId).getOrElse("none")}\n")
      builder.append(s"Child nodes: [${cs.map(_.ppId).mkString(", ")}]\n")

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

  /**
    * [Certify] Use the accumulated non-backtracked derivations to populate the CertTree
    * @param trace the trace
    * @return the root CertTree node
    */
  def fromTrace(trace: ProofTraceCert): Node = {
    def traverse(on: OrNode): Node = {
      val ans = trace.childAnds(on)
      if (ans.isEmpty) {
        // Cached result was used; search for the same goal in previously encountered nodes
        val n = trace.cachedGoals(on)
        traverse(n)
      } else {
        // Candidate derivations exist; find and process the correct one
        val n = for {
          an <- ans
          childOrs = trace.childOrs(an)
        } yield {
          val node = Node(on.id, on.goal, an.kont, an.rule)
          val children = childOrs.map(traverse)
          parentMap ++= children.map(_ -> node)
          childrenMap(node) = children
          node
        }
        assert(n.nonEmpty, s"No successful derivations found for goal ${on.id}")
        n.head
      }
    }
    clear()
    trace.pruneFailed()
    traverse(trace.root)
  }

  // [Certify]: Maintain a certification tree as a pair of bidirectional hash maps
  private val childrenMap: mutable.Map[Node, Seq[Node]] = mutable.Map.empty
  private val parentMap: mutable.Map[Node, Node] = mutable.Map.empty
  def root: Option[Node] = get(Vector())

  def get(id: NodeId): Option[Node] = {
    childrenMap.keys.find(_.nodeId == id)
  }

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
