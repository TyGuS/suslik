package org.tygus.suslik.certification.targets.coq.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.language.Statements._
import org.tygus.suslik.certification.targets.coq.logic.Proof._
import org.tygus.suslik.certification.targets.coq.translation.Translation._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.FailRules.AbduceBranch
import org.tygus.suslik.synthesis.rules.LogicalRules._
import org.tygus.suslik.synthesis.rules.OperationalRules._
import org.tygus.suslik.synthesis.rules.UnfoldingRules._

object ProgramTranslation {
  type CStmtProducer = Producer[CStatement]

  private case class TraversalItem(node: CertTree.Node, stmt: Statement) extends Traversable

  def translate(node: CertTree.Node, proc: Procedure, goal: CGoal): CStatement = {
    val traversalItem = TraversalItem(node, proc.body)
    traverseStmt(traversalItem, _.head)
  }

  private def joinCStmtProducer(steps: List[TraversalItem], kont: CStmtProducer): CStmtProducer =
    joinProducer[CStatement, TraversalItem](traverseStmt)(steps, kont)

  private def seqCompProducer(s: CStatement): CStmtProducer = {
    case hd :: _ => CSeqComp(s, hd)
    case Nil => s
  }

  private def openProducer(selectors: Seq[CExpr]): CStmtProducer = stmts =>
    if (stmts.length == 1) stmts.head else {
      val cond_branches = selectors.zip(stmts).reverse
      val ctail = cond_branches.tail
      val finalBranch = cond_branches.head._2
      ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => CIf(c, tb, eb).simplify }
    }

  private def guardedProducer(cond: CExpr): CStmtProducer = stmts =>
    CGuarded(cond, stmts.head, stmts.last)

  private def deriveCStmtProducer(item: TraversalItem, currStmt: Option[Statement]): Option[CStmtProducer] = {
    val node = item.node

    val footprint = node.consume
    val stmtProducer = unwrapStmtProducer(node.kont)
    (node.rule, stmtProducer) match {
      case (EmpRule, _) =>
        Some(seqCompProducer(CSkip))
      case (ReadRule, PrependProducer(Load(to, _, _, _))) =>
        currStmt match {
          case Some(Load(to1, tpe, from, offset)) if to.name.startsWith(to1.name) =>
            val s = CLoad(CVar(to.name), translateSSLType(tpe), CVar(from.name), offset)
            Some(seqCompProducer(s))
          case _ =>
            None // bound variable was eliminated by SeqComp.simplify
        }
      case (WriteRule, PrependProducer(Store(to, offset, e))) =>
        val s = CStore(CVar(to.name), offset, translateExpr(e))
        Some(seqCompProducer(s))
      case (FreeRule, PrependProducer(Free(v))) =>
        footprint.pre.blocks.find(_.loc == v).map { b =>
          val s = (1 until b.sz).foldLeft[CStatement](CFree(CVar(v.name))){
            (acc, n) => CSeqComp(CFree(CVar(v.name), n), acc)
          }
          seqCompProducer(s)
        }
      case (CallRule, PrependProducer(Call(fun, args, _))) =>
        val s = CCall(CVar(fun.name), args.map(translateExpr))
        val cstmt = seqCompProducer(s)
        Some(cstmt)
      case (Open, BranchProducer(selectors)) =>
        val cstmt = openProducer(selectors.map(translateExpr))
        Some(cstmt)
      case (AbduceBranch, GuardedProducer(cond, _)) =>
        val cstmt = guardedProducer(translateExpr(cond))
        Some(cstmt)
      case _ =>
        None // rule has no effect on certification
    }
  }

  @scala.annotation.tailrec
  private def traverseStmt(item: TraversalItem, kont: CStmtProducer): CStatement = {
    val (currStmt, nextStmts) = expandStmt(item.stmt)
    val childNodes = item.node.children
    val (nextTraversalItems, nextKont) = deriveCStmtProducer(item, currStmt) match {
      case Some(nextStmtKont) =>
        val nextTraversalItems = childNodes.zip(nextStmts).map(i => TraversalItem(i._1, i._2))
        val nextKont = composeProducer[CStatement](nextStmtKont, kont)
        (nextTraversalItems, nextKont)
      case _ =>
        (childNodes.map(TraversalItem(_, item.stmt)), kont)
    }

    nextTraversalItems match {
      case hd :: tl =>
        traverseStmt(hd, joinCStmtProducer(tl, nextKont))
      case Nil =>
        nextKont(List.empty)
    }
  }
}
