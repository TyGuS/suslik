package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.StatementProducers._
import org.tygus.suslik.certification.targets.htt.language.Statements._
import org.tygus.suslik.certification.targets.htt.logic.Proof._
import org.tygus.suslik.certification.targets.htt.translation.Translation._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.synthesis._

object ProgramTranslation {
  private case class TraversalItem(node: CertTree.Node) extends Traversable

  def translate(node: CertTree.Node, proc: Procedure, goal: CGoal): CStatement = {
    val traversalItem = TraversalItem(node)
    traverseStmt(traversalItem, IdCStmtProducer)
  }

  def traverseStmt(item: TraversalItem, kont: CStmtProducer): CStatement = {
    def translateOperation(s: Statement): CStatement = s match {
      case Skip =>
        CSkip
      case Load(to, tpe, from, offset) =>
        CLoad(CVar(to.name), translateSSLType(tpe), CVar(from.name), offset)
      case Store(to, offset, e) =>
        CStore(CVar(to.name), offset, translateExpr(e))
      case Malloc(to, tpe, sz) =>
        CMalloc(CVar(to.name), translateSSLType(tpe), sz)
      case Free(v) =>
        val block = item.node.footprint.pre.sigma.blocks.find(_.loc == v)
        assert(block.nonEmpty)
        CFree(CVar(v.name), block.get.sz)
      case Call(v, args, _) =>
        CCall(CVar(v.name), args.map(translateExpr))
    }

    def translateProducer(stmtProducer: StmtProducer): CStmtProducer = stmtProducer match {
      case ChainedProducer(p1, p2) =>
        val k1 = translateProducer(p1)
        val k2 = translateProducer(p2)
        k1 >> k2
      case PartiallyAppliedProducer(p, _) =>
        translateProducer(p)
      case ConstProducer(s) =>
        val stmt = translateOperation(s)
        ConstCStmtProducer(stmt)
      case PrependProducer(s) =>
        val stmt = translateOperation(s)
        PrependCStmtProducer(stmt)
      case BranchProducer(selectors) =>
        BranchCStmtProducer(selectors.map(translateExpr))
      case GuardedProducer(cond, _) =>
        GuardedCStmtProducer(translateExpr(cond))
      case _ =>
        IdCStmtProducer
    }

    def generateNextItems: Seq[TraversalItem] =
      item.node.children.map(n => TraversalItem(n))

    def updateProducerPost(nextItems: Seq[TraversalItem], nextKont: CStmtProducer): CStmtProducer = nextKont match {
      case _: Branching =>
        nextItems.tail.foldLeft(nextKont >> kont) {
          case (foldedP, item) => FoldCStmtProducer(traverseStmt, item, foldedP)
        }
      case _ =>
        nextKont >> kont
    }

    // generated nested continuations for children
    val p = translateProducer(item.node.kont).simplify
    val nextItems = generateNextItems
    val nextKont = updateProducerPost(nextItems, p).simplify

    nextItems.headOption match {
      case Some(childHead) =>
        traverseStmt(childHead, nextKont)
      case None =>
        nextKont(Nil)
    }
  }
}
