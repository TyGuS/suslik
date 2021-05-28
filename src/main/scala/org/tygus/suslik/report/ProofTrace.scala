package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}

import org.tygus.suslik.language.Expressions
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.Memoization
import org.tygus.suslik.synthesis.Memoization.GoalStatus
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import upickle.default.{macroRW, ReadWriter => RW}


sealed abstract class ProofTrace {
  import ProofTrace._
  def add(node: OrNode) { }
  def add(node: AndNode, nChildren: Int) { }
  def add(at: NodeId, status: GoalStatus, from: Option[String] = None) { }
  def add(result: Rules.RuleResult, parent: OrNode) { }
  def add(backlink: BackLink) { }
  def add(ruleTrail: RuleTrail) { }
}

object ProofTrace {
  case class BackLink(bud: Goal, companion: Goal)
  case class RuleTrail(from: Goal, to: Seq[Goal], rule: SynthesisRule,
                       subst: Map[String, String])

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

  override def add(at: NodeId, status: GoalStatus, from: Option[String] = None): Unit = {
    val st = status match {
      case Memoization.Succeeded(_) => Succeeded
      case Memoization.Failed => Failed
      case _ => throw new RuntimeException(s"cannot serialize $status")
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

  override def add(backlink: BackLink) {
    writeObject(BackLinkEntry("BackLink",
        backlink.bud.label.pp, backlink.companion.label.pp))
  }

  override def add(ruleTrail: RuleTrail) {
    writeObject(RuleTrailEntry("RuleTrail",
      ruleTrail.from.label.pp, ruleTrail.to.map(_.label.pp),
      ruleTrail.rule.toString, ruleTrail.subst))
  }
}


object ProofTraceJson {

  case class NodeEntry(id: Vector[Int], tag: String, pp: String, goal: GoalEntry,
                       nChildren: Int, cost: Int)
  object NodeEntry {
    implicit val rw: RW[NodeEntry] = macroRW
  }

  case class GoalEntry(id: GoalEntry.Id,
                       pre: String,
                       post: String,
                       sketch: String,
                       programVars: Seq[(String, String)],
                       existentials: Seq[(String, String)],
                       ghosts: Seq[(String, String)])
  object GoalEntry {
    type Id = String
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

  case class BackLinkEntry(tag: String, bud: String, companion: String)
  object BackLinkEntry {
    implicit val rw: RW[BackLinkEntry] = macroRW
  }

  case class RuleTrailEntry(tag: String,
                            from: GoalEntry.Id,
                            to: Seq[GoalEntry.Id],
                            ruleName: String,
                            subst: Map[String, String])
  object RuleTrailEntry {
    implicit val rw: RW[RuleTrailEntry] = macroRW
  }
}
