package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}

import org.tygus.suslik.language.Expressions
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.Memoization
import org.tygus.suslik.synthesis.Memoization.{GoalStatus}
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.rules.Rules
import upickle.default.{macroRW, ReadWriter => RW}


sealed abstract class ProofTrace {
  def add(node: OrNode) { }
  def add(node: AndNode, nChildren: Int) { }
  def add(at: NodeId, status: GoalStatus, from: Option[String] = None) { }
  def add(result: Rules.RuleResult, parent: OrNode) { }
}

object ProofTraceNone extends ProofTrace

class ProofTraceJson(val outputFile: File) extends ProofTrace {
  import ProofTraceJson._

  val writer = new BufferedWriter(new FileWriter(outputFile))

  def this(outputFilename: String) = this(new File(outputFilename))

  private def writeObject[T](t: T)(implicit w: upickle.default.Writer[T]): Unit = {
    writer.write(upickle.default.write(t))
    writer.write("\n\n")
    writer.flush()
  }

  override def add(node: OrNode): Unit =
    writeObject(NodeEntry(node.id, "OrNode", node.pp(), GoalEntry(node.goal), -1))

  override def add(node: AndNode, nChildren: Int): Unit =
    writeObject(NodeEntry(node.id, "AndNode", node.pp(), null, nChildren))

  override def add(at: NodeId, status: GoalStatus, from: Option[String] = None): Unit = {
    val st = status match {
      case Memoization.Succeeded(_) => Succeeded
      case Memoization.Failed => Failed
      case _ => throw new RuntimeException(s"cannot serialize ${status}")
    }
    writeObject(StatusEntry(at, st.copy(from = from)))
  }

  override def add(result: Rules.RuleResult, parent: OrNode) {
    if (result.subgoals.isEmpty) {
      val resolution = AndNode(-1 +: parent.id, parent, result)
      val status = Memoization.Succeeded(null) // ignoring solution, sry
      add(resolution, 0)
      add(resolution.id, status)
      add(parent.id, status)
    }
  }
}


object ProofTraceJson {

  case class NodeEntry(id: Vector[Int], tag: String, pp: String, goal: GoalEntry, nChildren: Int)
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
  val Succeeded = GoalStatusEntry("Succeeded")
  val Failed = GoalStatusEntry("Failed")

  object GoalStatusEntry {
    implicit val readWriter: RW[GoalStatusEntry] = macroRW
  }

  case class StatusEntry(at: Vector[Int], status: GoalStatusEntry)
  object StatusEntry {
    implicit val rw: RW[StatusEntry] = macroRW
  }
}
