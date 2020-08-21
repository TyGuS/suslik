package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}

import org.tygus.suslik.language.Expressions
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.Memoization
import org.tygus.suslik.synthesis.Memoization.GoalStatus
import org.tygus.suslik.synthesis.SearchTree.{AndNode, OrNode, SearchNode}
import org.tygus.suslik.synthesis.rules.Rules
import upickle.default.{macroRW, ReadWriter => RW}


sealed abstract class ProofTrace {
  import ProofTrace._
  def add(node: OrNode) { }
  def add(node: AndNode, nChildren: Int) { }
  def add(node: SearchNode, status: GoalStatus, from: Option[String] = None) { }
  def add(result: Rules.RuleResult, parent: OrNode) { }
  def add(backlink: BackLink) { }
}

object ProofTrace {
  case class BackLink(bud: Goal, companion: Goal)

  var current: ProofTrace = ProofTraceNone  // oops, not thread-safe
}

object ProofTraceNone extends ProofTrace

class ProofTraceJson(val outputFile: File) extends ProofTrace {
  import ProofTrace._
  import ProofTraceJson._

  val writer = new BufferedWriter(new FileWriter(outputFile))

  def this(outputFilename: String) = this(new File(outputFilename))

  private def writeObject[T](t: T)(implicit w: upickle.default.Writer[T]): Unit = {
    writer.write(upickle.default.write(t))
    writer.write("\n\n")
    writer.flush()
  }

  override def add(node: OrNode): Unit =
    writeObject(NodeEntry(node.id, "OrNode", node.pp(), GoalEntry(node.goal), -1, node.cost))

  override def add(node: AndNode, nChildren: Int): Unit =
    writeObject(NodeEntry(node.id, "AndNode", node.pp(), null, nChildren, -1))

  override def add(node: SearchNode, status: GoalStatus, from: Option[String] = None): Unit = {
    val st = status match {
      case Memoization.Succeeded(_) => Succeeded
      case Memoization.Failed => Failed
      case _ => throw new RuntimeException(s"cannot serialize $status")
    }
    writeObject(StatusEntry(node.id, st.copy(from = from)))
  }

  override def add(result: Rules.RuleResult, parent: OrNode) {
    if (result.subgoals.isEmpty) {
      val resolution = AndNode(-1 +: parent.id, parent, result)
      val status = Memoization.Succeeded(null) // ignoring solution, sry
      add(resolution, 0)
      add(resolution, status)
      add(parent, status)
    }
  }

  override def add(backlink: BackLink) {
    writeObject(CyclicEntry(
      BackLinkEntry(backlink.bud.label.pp, backlink.companion.label.pp)))
  }
}


object ProofTraceJson {

  case class NodeEntry(id: Vector[Int], tag: String, pp: String, goal: GoalEntry,
                       nChildren: Int, cost: Int)
  object NodeEntry {
    implicit val rw: RW[NodeEntry] = macroRW
  }

  case class GoalEntry(id: String,
                       pre: String,
                       post: String,
                       sketch: String,
                       programVars: Seq[(String, String)],
                       existentials: Seq[(String, String)],
                       ghosts: Seq[(String, String)])
  object GoalEntry {
    implicit val rw: RW[GoalEntry] = macroRW

    def apply(goal: Goal): GoalEntry = GoalEntry(goal.label.pp,
      goal.pre.pp, goal.post.pp, goal.sketch.pp,
      vars(goal, goal.programVars), vars(goal, goal.existentials),
      vars(goal, goal.universalGhosts))

    private def vars(goal: Goal, vs: Iterable[Expressions.Var]) =
      vs.map(v => (goal.getType(v).pp, v.pp)).toSeq
  }

  case class GoalStatusEntry(tag: String, from: Option[String] = None)
  val Succeeded = new GoalStatusEntry("Succeeded")
  val Failed = new GoalStatusEntry("Failed")

  object GoalStatusEntry {
    implicit val readWriter: RW[GoalStatusEntry] = macroRW
  }

  case class StatusEntry(at: Vector[Int], status: GoalStatusEntry)
  object StatusEntry {
    implicit val rw: RW[StatusEntry] = macroRW
  }

  case class CyclicEntry(backlink: BackLinkEntry)
  object CyclicEntry {
    implicit val rw: RW[CyclicEntry] = macroRW
  }

  case class BackLinkEntry(bud: String, companion: String)
  object BackLinkEntry {
    implicit val rw: RW[BackLinkEntry] = macroRW
  }
}

// [Certify] Collects non-backtracked SearchTree nodes (and their ancestors), used to populate the CertTree
class ProofTraceCert extends ProofTrace {
  import scala.collection.mutable

  // The candidate derivations encountered for each OrNode
  private val derivations: mutable.Map[OrNode, Seq[AndNode]] = mutable.Map.empty
  // The solved subgoals for each AndNode
  private val fulfilledSubgoals: mutable.Map[AndNode, Seq[OrNode]] = mutable.Map.empty
  // The number of subgoals that need to be solved for each AndNode
  private val numSubgoals: mutable.Map[AndNode, Int] = mutable.Map.empty

  var root: OrNode = _

  override def add(node: AndNode, nChildren: Int): Unit = numSubgoals(node) = nChildren

  override def add(node: SearchNode, status: GoalStatus, from: Option[String] = None): Unit = node match {
    case node: OrNode => if (status.isInstanceOf[Memoization.Succeeded]) addOr(node)
    case _ =>
  }

  override def add(result: Rules.RuleResult, parent: OrNode): Unit = {
    val an = AndNode(-1 +: parent.id, parent, result)
    addAnd(an)
  }

  private def addAnd(node: AndNode): Unit = {
    val parentOr = node.parent
    derivations.get(parentOr) match {
      case Some(ans) => derivations(parentOr) = ans :+ node
      case None => derivations(parentOr) = Seq(node)
    }
    addOr(parentOr)  // Continue adding ancestors
  }

  private def addOr(node: OrNode): Unit = node.parent match {
    case Some(parentAn) =>
      fulfilledSubgoals.get(parentAn) match {
        case Some(ons) =>
          if (!ons.contains(node)) {
            // Make sure new goal respects ordering of subgoals by goal id
            val idx = scala.math.min(node.id.head, ons.length)
            val (fst, snd) = ons.splitAt(idx)
            fulfilledSubgoals(parentAn) = fst ++ Seq(node) ++ snd
          }  // Terminate (node already encountered)
        case None =>
          fulfilledSubgoals(parentAn) = Seq(node)
          addAnd(parentAn)  // Continue adding ancestors
      }
    case None =>
      root = node  // Terminate (node is root)
  }

  // Retrieve candidate derivations for a goal
  def childAnds(node: OrNode): Seq[AndNode] = derivations.getOrElse(node, Seq.empty)

  // Retrieve subgoals for a derivation if it succeeded
  def childOrs(node: AndNode): Option[Seq[OrNode]] = fulfilledSubgoals.get(node) match {
    // All subgoals were solved, so this derivation was successful
    case Some(ors) if ors.length == numSubgoals(node) => Some(ors)
    // This is a terminal node
    case None => Some(Seq.empty)
    // This is a non-terminal node, but not all subgoals were solved
    case _ => None
  }
}
