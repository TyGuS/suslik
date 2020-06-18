package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}

import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.Memoization
import org.tygus.suslik.synthesis.Memoization.GoalStatus
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import upickle.default.{macroRW, ReadWriter => RW}


class ProofTrace(val outputFile: File) {
  import ProofTrace._

  val writer = new BufferedWriter(new FileWriter(outputFile))

  def this(outputFilename: String) = this(new File(outputFilename))

  private def writeObject[T](t: T)(implicit w: upickle.default.Writer[T]): Unit = {
    writer.write(upickle.default.write(t));
    writer.write("\n\n");
    writer.flush();
  }

  def add(node: OrNode) =
    writeObject(NodeEntry(node.id, "OrNode", node.pp(), GoalEntry(node.goal)))

  def add(node: AndNode) =
    writeObject(NodeEntry(node.id, "AndNode", node.pp(), null))

  def add(at: NodeId, status: GoalStatus) = {
    val st = status match {
      case Memoization.Succeeded(_) => Succeeded
      case Memoization.Failed => Failed
      case _ => throw new RuntimeException(s"cannot serialize ${status}")
    }
    writeObject(StatusEntry(at, st))
  }

}


object ProofTrace {

  case class NodeEntry(id: Vector[Int], tag: String, pp: String, goal: GoalEntry)
  object NodeEntry {
    implicit val rw: RW[NodeEntry] = macroRW
  }

  case class GoalEntry(pre: String,
                       post: String,
                       sketch: String,
                       programVars: Seq[(String, String)],
                       existentials: Seq[(String, String)])
  object GoalEntry {
    implicit val rw: RW[GoalEntry] = macroRW

    def apply(goal: Goal): GoalEntry = GoalEntry(goal.pre.pp, goal.post.pp, goal.sketch.pp,
      goal.programVars.map(v => (goal.getType(v).pp, v.pp)),
      goal.existentials.map(v => (goal.getType(v).pp, v.pp)).toSeq)
  }

  case class GoalStatusEntry(tag: String)
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
