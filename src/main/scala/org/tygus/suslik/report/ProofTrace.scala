package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}
import scala.language.implicitConversions
import scala.util.DynamicVariable
import org.tygus.suslik.language.{Expressions, PrettyPrinting}
import org.tygus.suslik.language.Expressions.{ExprSubst, Subst}
import org.tygus.suslik.logic.{Block, Heaplet, PointsTo, SApp, Specifications}
import org.tygus.suslik.logic.Specifications.{Goal, SuspendedCallGoal}
import org.tygus.suslik.synthesis.Memoization
import org.tygus.suslik.synthesis.Memoization.GoalStatus
import org.tygus.suslik.synthesis.SearchTree.{AndNode, OrNode, SearchNode}
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import upickle.default.{macroRW, ReadWriter => RW}

import scala.annotation.tailrec
import scala.language.implicitConversions


sealed abstract class ProofTrace {
  import ProofTrace._
  def add(node: OrNode) { }
  def add(node: AndNode, nChildren: Int) { }
  def add(node: SearchNode, status: GoalStatus, from: Option[String] = None) { }
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

  object DerivationTrail {
    def withSubst[A <: PrettyPrinting, B <: PrettyPrinting](from: Goal, to: Seq[Goal],
                                                            rule: SynthesisRule,
                                                            subst: Map[A, B]): DerivationTrail =
      apply(from, to, rule, subst.map { case (k, v) => k.pp -> (v.pp: OrVec) })
  }

  def current: ProofTrace = _current.value
  def current_=(trace: ProofTrace): Unit = _current.value = trace

  def using[T](trace: ProofTrace)(op: => T): T = _current.withValue(trace)(op)

  // need to be thread-local, for `SynthesisServer`
  private val _current = new DynamicVariable[ProofTrace](ProofTraceNone)
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

  override def add(node: SearchNode, status: GoalStatus, from: Option[String] = None): Unit = {
    val st = status match {
      case Memoization.Succeeded(_, _) => Succeeded
      case Memoization.Failed => Failed
      case _ => throw new RuntimeException(s"cannot serialize $status")
    }
    writeObject(StatusEntry(node.id, st.copy(from = from)))
  }

  override def add(result: Rules.RuleResult, parent: OrNode) {
    if (result.subgoals.isEmpty) {
      val resolution = AndNode(-1 +: parent.id, parent, result)
      val status = Memoization.Succeeded(null, null) // ignoring solution, sry
      add(resolution, 0)
      add(resolution, status)
      add(parent, status)
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
                       ghosts: Seq[(String, String)],
                       callGoal: Option[GoalEntry] = None /* suspended call goal */)
  object GoalEntry {
    type Id = String
    implicit val rw: RW[GoalEntry] = macroRW

    def apply(goal: Goal): GoalEntry = apply(goal.label.pp,
      AssertionEntry(goal.pre), AssertionEntry(goal.post), goal.sketch.pp,
      vars(goal, goal.programVars), vars(goal, goal.existentials),
      vars(goal, goal.universalGhosts), goal.callGoal.map(callInfo(goal, _)))

    private def vars(goal: Goal, vs: Iterable[Expressions.Var]) =
      vs.map(v => (goal.getType(v).pp, v.pp)).toSeq

    private def callInfo(goal: Goal, callGoal: SuspendedCallGoal) = {
      val funSpec = goal.ancestorWithLabel(callGoal.call.companion.get).get.toFunSpec
      val toActual = compose(callGoal.companionToFresh, callGoal.freshToActual)
      apply(callGoal.call.companion.get.pp,
        AssertionEntry(funSpec.pre.subst(toActual)),
        AssertionEntry(funSpec.post.subst(toActual)), callGoal.actualCall.pp,
        Seq(), Seq(), Seq())
    }

    /** @oops copied from PureLogicUtils */
    def compose(subst1: Subst, subst2: Subst): Subst = subst1.map { case (k, e) => k -> e.subst(subst2) }
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
      case ("{}", elems) => SetLiteral(elems.map(_.toExpr).toList)
      case ("ite", Seq(cond, left, right)) => IfThenElse(cond.toExpr, left.toExpr, right.toExpr)
      case ("Unknown", Leaf(name) +: params :+ subst) =>
        Unknown(name, params.map(_.toVar).toSet, subst.toSubst)
      case (kop, Seq(arg)) =>
        UNOP.get(kop) match {
          case Some(op) => UnaryExpr(op, arg.toExpr)
          case _ => throw new RuntimeException(s"unknown unary operator: '${kop}'")
        }
      case (kop, Seq(arg0, arg1)) =>
        BINOP.get(kop) match {
          case Some(op: BinOp) => BinaryExpr(op, arg0.toExpr, arg1.toExpr)
          case Some(op: OverloadedBinOp) => OverloadedBinaryExpr(op, arg0.toExpr, arg1.toExpr)
          case _ => throw new RuntimeException(s"unknown binary operator: '${kop}'")
        }
      case _ => throw new RuntimeException(s"error in expression: '${this}'")
    }

    def toVar: Var = toExpr.asInstanceOf[Var]

    def toSubst: Subst = subtrees.map { case AST("↦", Seq(v, e)) => v.toVar -> e.toExpr } .toMap

    def toHeaplet: Heaplet = ???
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
      case UnaryExpr(op, arg) => labelOf(op) -: fromExpr(arg)
      case BinaryExpr(op, left, right) => AST(labelOf(op), Seq(left, right).map(fromExpr))
      case OverloadedBinaryExpr(op, left, right) => AST(labelOf(op), Seq(left, right).map(fromExpr))
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
      case SApp(pred, args, tag, card) => AST("SApp",
        Seq(AST(pred), AST("()", args.map(fromExpr)), AST(tag.pp), fromExpr(card)))
    }

    object Leaf {
      def unapply(t: AST): Option[String] =
        if (t.subtrees.isEmpty) Some(t.root) else None
    }

    /* Operator serialization */
    import Expressions._
    val UNOP = Map("not" -> OpNot, "u-" -> OpUnaryMinus, "lower" -> OpLower, "upper" -> OpUpper)
    val BINOP = Map("==" -> OpOverloadedEq, "<=" -> OpOverloadedLeq, "-" -> OpOverloadedMinus,
      "+" -> OpOverloadedPlus, "*" -> OpOverloadedStar, "in" -> OpOverloadedIn,
      "!=" -> OpNotEqual, ">" -> OpGt, ">=" -> OpGeq,
      "==[bool]" -> OpBoolEq, "->" -> OpImplication,
      "<=[int]" -> OpLeq, "<" -> OpLt, "&&" -> OpAnd, "||" -> OpOr,
      "+[int]" -> OpPlus, "-[int]" -> OpMinus, "*[int]" -> OpMultiply,
      "++" -> OpUnion, "--" -> OpDiff, "*[set[int]]" -> OpIntersect,
      "in[int]" -> OpIn, "==[loc]" -> OpEq,
      "==[set[int]]" -> OpSetEq, "<=[set[int]]" -> OpSubset
      /** @todo interval operators */
    )

    def labelOf(op: UnOp): String = mustGet(UNOP, op)
    def labelOf(op: BinOp): String = mustGet(BINOP, op)
    def labelOf(op: OverloadedBinOp): String = mustGet(BINOP, op)

    private def mustGet[A](m: Map[String, A], op: A): String =
      m.toSeq.find(_._2 == op).getOrElse
        { throw new NoSuchElementException(s"operator not found: ${op}") } ._1
  }
}

// [Certify] Collects non-backtracked SearchTree nodes (and their ancestors), used to populate the CertTree
class ProofTraceCert extends ProofTrace {
  import scala.collection.mutable

  val derivations: mutable.HashMap[OrNode, Seq[(Boolean, AndNode)]] = mutable.HashMap.empty
  val subgoals: mutable.HashMap[AndNode, Seq[(Boolean, OrNode)]] = mutable.HashMap.empty
  val failed: mutable.Set[OrNode] = mutable.Set.empty
  val succeeded: mutable.Set[OrNode] = mutable.Set.empty
  val cachedGoals: mutable.HashMap[OrNode, OrNode] = mutable.HashMap.empty
  var root: OrNode = _

  override def add(node: OrNode): Unit = {
    node.parent match {
      case None => root = node
      case Some(an) =>
        subgoals.get(an) match {
          case None => subgoals(an) = Seq((false, node))
          case Some(ons) => subgoals(an) = ons :+ (false, node)
        }
    }
  }

  override def add(node: AndNode, nChildren: Int): Unit = {
    derivations.get(node.parent) match {
      case None => derivations(node.parent) = Seq((false, node))
      case Some(ans) => derivations(node.parent) = ans :+ (false, node)
    }
  }

  override def add(node: SearchNode, status: GoalStatus, from: Option[String] = None): Unit = (node, status) match {
    case (node: OrNode, Memoization.Succeeded(_, id)) =>
      succeeded.add(node)
      derivations.keys.find(_.id == id) match {
        case Some(succeededOr) => cachedGoals(node) = succeededOr
        case None => assert(false, s"Couldn't find cached OrNode with id $id")
      }
    case (node: OrNode, Memoization.Failed) =>
      failed.add(node)
    case _ =>
  }

  override def add(result: Rules.RuleResult, parent: OrNode): Unit = {
    if (result.subgoals.isEmpty) {
      val an = AndNode(-1 +: parent.id, parent, result)
      derivations.get(parent) match {
        case None => derivations(parent) = Seq((true, an))
        case Some(ans) => derivations(parent) = ans :+ (true, an)
      }
      succeeded.add(parent)
    }
  }

  @tailrec
  private def handleFail(node: OrNode, original: OrNode): Unit = node.parent match {
    case None =>
    case Some(an) =>
      derivations(an.parent) = derivations(an.parent).filterNot(_._2.id == an.id)
      if (!derivations(an.parent).exists(_._1)) {
        // This goal has no more viable candidate derivations, so can prune further up the tree
        handleFail(an.parent, original)
      }
  }

  @tailrec
  private def handleSuccess(node: OrNode): Unit = node.parent match {
    case None =>
    case Some(an) =>
      val newOns = updatePeerStatus(node, subgoals(an), newStatus = true)
      subgoals(an) = newOns
      if (newOns.forall(_._1)) {
        derivations(an.parent) = updatePeerStatus(an, derivations(an.parent), newStatus = true)
        handleSuccess(an.parent)
      }
  }

  def pruneFailed(): Unit = {
    for (s <- succeeded) {
      handleSuccess(s)
    }
    for (f <- failed) {
      handleFail(f, f)
    }
  }

  private def updatePeerStatus[T <: SearchNode](node: T, peers: Seq[(Boolean, T)], newStatus: Boolean): Seq[(Boolean, T)] =
    peers.map { case (status, n) => if (n.id == node.id) (newStatus, n) else (status, n )}

  def childAnds(node: OrNode): Seq[AndNode] = {
    derivations.getOrElse(node, Seq.empty).filter(_._1).map(_._2)
  }
  def childOrs(node: AndNode): Seq[OrNode] =
    subgoals.getOrElse(node, Seq.empty).filter(_._1).map(_._2)
}
