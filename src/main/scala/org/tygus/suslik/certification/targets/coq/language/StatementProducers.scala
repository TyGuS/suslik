package org.tygus.suslik.certification.targets.coq.language

import org.tygus.suslik.certification.targets.coq.language.Expressions.CExpr
import org.tygus.suslik.certification.targets.coq.language.Statements.{CGuarded, CIf, CSeqComp, CStatement}

object StatementProducers {
  type Kont = Seq[CStatement] => CStatement

  trait Branching

  sealed abstract class CStmtProducer {
    val arity: Int
    val fn: Kont

    def apply(children: Seq[CStatement]): CStatement = {
      assert(children.lengthCompare(arity) == 0, s"Producer expects $arity children and got ${children.length}")
      fn(children)
    }

    def >>(p: CStmtProducer): CStmtProducer = {
      ChainedCStmtProducer(this, p)
    }

    def partApply(s: CStatement): CStmtProducer = {
      PartiallyAppliedCStmtProducer(this, s)
    }

    def simplify: CStmtProducer = this match {
      case ChainedCStmtProducer(p1, IdCStmtProducer) => p1.simplify
      case ChainedCStmtProducer(IdCStmtProducer, p2) => p2.simplify
      case ChainedCStmtProducer(_, p2@ConstCStmtProducer(_)) => p2.simplify
      case _ => this
    }
  }

  case class ChainedCStmtProducer(p1: CStmtProducer, p2: CStmtProducer) extends CStmtProducer {
    val arity: Int = p1.arity + p2.arity - 1
    val fn: Kont = stmts => {
      val (stmts1, stmts2) = stmts.splitAt(p1.arity)
      val s = p1.fn(stmts1)
      p2.fn(s +: stmts2)
    }
  }

  case class PartiallyAppliedCStmtProducer(p: CStmtProducer, s: CStatement) extends CStmtProducer with Branching {
    val arity: Int = p.arity - 1
    val fn: Kont = stmts => {
      p.apply(s +: stmts)
    }
  }

  case object IdCStmtProducer extends CStmtProducer {
    val arity: Int = 1
    val fn: Kont = _.head
  }

  case class ConstCStmtProducer(s: CStatement) extends CStmtProducer {
    val arity: Int = 0
    val fn: Kont = _ => s
  }

  case class PrependCStmtProducer(s: CStatement) extends CStmtProducer {
    val arity: Int = 1
    val fn: Kont = stmts => CSeqComp(s, stmts.head).simplify
  }

  case class AppendCStmtProducer(s: CStatement) extends CStmtProducer {
    val arity: Int = 1
    val fn: Kont = stmts => CSeqComp(stmts.head, s).simplify
  }

  case class BranchCStmtProducer(selectors: Seq[CExpr]) extends CStmtProducer with Branching {
    val arity: Int = selectors.length
    val fn: Kont = stmts =>
      if (stmts.length == 1) stmts.head else {
        val cond_branches = selectors.zip(stmts).reverse
        val ctail = cond_branches.tail
        val finalBranch = cond_branches.head._2
        ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => CIf(c, tb, eb).simplify }
      }
  }

  case class GuardedCStmtProducer(cond: CExpr) extends CStmtProducer with Branching {
    val arity: Int = 2
    val fn: Kont = stmts => CGuarded(cond, stmts.head, stmts.last)
  }

  case class FoldCStmtProducer[T](op: (T, CStmtProducer) => CStatement, item: T, bp: CStmtProducer) extends CStmtProducer {
    val arity: Int = 1
    val fn: Kont = steps => {
      // partially apply a produced step to the BranchProducer of the downstream `bp`
      @scala.annotation.tailrec
      def isBase(curr: CStmtProducer): Boolean = curr match {
        case PartiallyAppliedCStmtProducer(p, _) => isBase(p)
        case _: Branching => true
        case _ => false
      }
      def update(curr: CStmtProducer): CStmtProducer = curr match {
        case FoldCStmtProducer(op, item, bp) => FoldCStmtProducer(op, item, update(bp))
        case ChainedCStmtProducer(p1, p2) => ChainedCStmtProducer(update(p1), update(p2))
        case _: PartiallyAppliedCStmtProducer | _: Branching if isBase(curr) => curr.partApply(steps.head)
        case _ => curr
      }
      op(item, update(bp))
    }
  }
}
