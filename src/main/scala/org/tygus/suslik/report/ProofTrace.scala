package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}
import org.tygus.suslik.language.Expressions
import org.tygus.suslik.logic.{Block, Heaplet, PointsTo, SApp, Specifications}
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.Memoization
import org.tygus.suslik.synthesis.Memoization.GoalStatus
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import upickle.default.{macroRW, ReadWriter => RW}

import scala.language.implicitConversions


sealed abstract class ProofTrace {
  import ProofTrace._
  def add(node: OrNode) { }
  def add(node: AndNode, nChildren: Int) { }
  def add(at: NodeId, status: GoalStatus, from: Option[String] = None) { }
  def add(result: Rules.RuleResult, parent: OrNode) { }
  def add(backlink: BackLink) { }
  def add(derivationTrail: DerivationTrail) { }
}

object ProofTrace {
  case class BackLink(bud: Goal, companion: Goal)

  abstract class OrVec()
  case class Single(s: String) extends OrVec
  case class Vec(ss: Seq[String]) extends OrVec

  object OrVec {
    implicit def orVecFromT(s: String): Single = Single(s)
    implicit def orVecFromSeq(s: Seq[String]): Vec = Vec(s)
  }

  case class DerivationTrail(from: Goal, to: Seq[Goal], rule: SynthesisRule,
                             subst: Map[String, OrVec])

  var current: ProofTrace = ProofTraceNone  // oops, not thread-safe
}

object ProofTraceNone extends ProofTrace

abstract class ProofTraceJson extends ProofTrace {
  import ProofTrace._
  import ProofTraceJson._

  protected def writeObject[T](t: T)(implicit w: upickle.default.Writer[T]): Unit

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

  override def add(derivationTrail: DerivationTrail) {
    val d = derivationTrail
    writeObject(DerivationTrailEntry("DerivationTrail",
      d.from.label.pp, d.to.map(_.label.pp), d.rule.toString, d.subst))
  }
}

class ProofTraceJsonFile(val outputFile: File) extends ProofTraceJson {
  val writer = new BufferedWriter(new FileWriter(outputFile))

  def this(outputFilename: String) = this(new File(outputFilename))

  override protected def writeObject[T](t: T)(implicit w: upickle.default.Writer[T]): Unit = {
    writer.write(upickle.default.write(t))
    writer.write("\n\n")
    writer.flush()
  }
}

object ProofTraceJson {

  case class NodeEntry(id: Vector[Int], tag: String, pp: String, goal: GoalEntry,
                       nChildren: Int, cost: Int)
  object NodeEntry {
    implicit val rw: RW[NodeEntry] = macroRW
  }

  case class GoalEntry(id: GoalEntry.Id,
                       pre: AssertionEntry,
                       post: AssertionEntry,
                       sketch: String,
                       programVars: Seq[(String, String)],
                       existentials: Seq[(String, String)],
                       ghosts: Seq[(String, String)])
  object GoalEntry {
    type Id = String
    implicit val rw: RW[GoalEntry] = macroRW

    def apply(goal: Goal): GoalEntry = apply(goal.label.pp,
      AssertionEntry(goal.pre), AssertionEntry(goal.post), goal.sketch.pp,
      vars(goal, goal.programVars), vars(goal, goal.existentials),
      vars(goal, goal.universalGhosts))

    private def vars(goal: Goal, vs: Iterable[Expressions.Var]) =
      vs.map(v => (goal.getType(v).pp, v.pp)).toSeq
  }

  case class AssertionEntry(pp: String, phi: Seq[AST], sigma: Seq[AST])
  object AssertionEntry {
    implicit val rw: RW[AssertionEntry] = macroRW

    def apply(a: Specifications.Assertion): AssertionEntry =
      apply(a.pp,
            a.phi.conjuncts.toSeq.map(AST.fromExpr),
            a.sigma.chunks.map(AST.fromHeaplet))
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

  case class BackLinkEntry(tag: String, bud: String, companion: String)
  object BackLinkEntry {
    implicit val rw: RW[BackLinkEntry] = macroRW
  }

  import upickle.default._
  import ProofTrace.{OrVec, Single, Vec}

  implicit val ovRW: RW[OrVec] =
    readwriter[ujson.Value].bimap[OrVec](
      { case Single(x) => x case Vec(v) => v },
      json => json.arrOpt match {
        case Some(v) => Vec(v.map(_.str))
        case None => Single(json.str)
      }
    )

  case class DerivationTrailEntry(tag: String,
                                  from: GoalEntry.Id,
                                  to: Seq[GoalEntry.Id],
                                  ruleName: String,
                                  subst: Map[String, OrVec])
  object DerivationTrailEntry {
    implicit val rw: RW[DerivationTrailEntry] = macroRW
  }


  case class AST(root: String, subtrees: Seq[AST]) {
    def -:(root: String): AST = AST(root, Seq(this))
    def :/(sub: Seq[AST]): AST = AST(root, subtrees ++ sub)

    import Expressions._
    import AST._

    def toExpr: Expr = (root, subtrees) match {
      case ("Var", Seq(Leaf(v))) => Var(v)
      case ("IntConst", Seq(Leaf(v))) => IntConst(Integer.parseInt(v))
      case ("BoolConst", Seq(Leaf(v))) => BoolConst(v == "true")
      case _ => throw new RuntimeException(s"error in expression: '${this}'")
    }
  }

  object AST {
    implicit val rw: RW[AST] = macroRW

    def apply(root: String): AST = apply(root, Seq())
    def apply(root: AnyVal): AST = apply(root.toString)

    import Expressions._

    def fromExpr(e: Expr): AST = e match {
      case Var(name) => "Var" -: AST(name)
      case IntConst(_) => "IntConst" -: AST(e.pp)
      case BoolConst(_) => "BoolConst" -: AST(e.pp)
      case UnaryExpr(op, arg) => op.pp -: fromExpr(arg)
      case BinaryExpr(op, left, right) => AST(op.pp, Seq(left, right).map(fromExpr))
      case SetLiteral(elems) => AST("{}", elems.map(fromExpr))
      case IfThenElse(cond, left, right) => AST("ite", Seq(cond, left, right).map(fromExpr))
      case Unknown(name, params, pendingSubst) =>
        AST("Unknown", AST(name) +: params.toSeq.map(fromExpr) :+ fromSubst(pendingSubst))
    }

    def fromSubst(subst: Subst): AST =
      AST("{}") :/
        subst.toSeq.map { case (v, e) => AST("↦", Seq(v, e).map(fromExpr)) }

    def fromHeaplet(heaplet: Heaplet): AST = heaplet match {
      case PointsTo(loc, offset, value) => AST("↦", Seq(fromExpr(loc), AST(offset), fromExpr(value)))
      case Block(loc, sz) => AST("[]", Seq(fromExpr(loc), AST(sz)))
      case SApp(pred, args, tag, card) => AST("SApp", AST(pred) +: args.map(fromExpr))
    }

    object Leaf {
      def unapply(t: AST): Option[String] =
        if (t.subtrees.isEmpty) Some(t.root) else None
    }
  }
}
