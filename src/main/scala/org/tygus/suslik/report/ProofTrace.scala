package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}

import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.{NodeId, OrNode}
import upickle.default.{macroRW, ReadWriter => RW}


class ProofTrace(val outputFile: File) {

  val writer = new BufferedWriter(new FileWriter(outputFile))

  def this(outputFilename: String) = this(new File(outputFilename))

  case class NodeEntry(id: Vector[Int], pp: String, goal: GoalEntry)
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

  def add(node: OrNode): Unit = {
    val o = NodeEntry(node.id, node.pp(), GoalEntry(node.goal))
    writer.write(upickle.default.write(o));
    writer.write("\n\n");
    writer.flush();
  }

}
