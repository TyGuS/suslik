package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.htt.program.StatementProducers._
import org.tygus.suslik.certification.targets.htt.program.Statements._
import org.tygus.suslik.certification.targets.htt.translation.Translation._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.synthesis._

object ProgramTranslation {
  def translate(node: CertTree.Node, proc: Procedure): CProcedure = {
    val stmtBody = traverseStmt(node, IdCStmtProducer)
    CProcedure(proc.name, translateType(proc.tp), proc.formals.map(translateParam), stmtBody)
  }

  def traverseStmt(node: CertTree.Node, kont: CStmtProducer): CStatement = {
    def translateOperation(s: Statement): CStatement = s match {
      case Skip =>
        CSkip
      case Load(to, tpe, from, offset) =>
        CLoad(translateVar(to), translateType(tpe), translateVar(from), offset)
      case Store(to, offset, e) =>
        CStore(translateVar(to), offset, translateExpr(e))
      case Malloc(to, tpe, sz) =>
        CMalloc(translateVar(to), translateType(tpe), sz)
      case Free(v) =>
        val block = node.footprint.pre.sigma.blocks.find(_.loc == v)
        assert(block.nonEmpty)
        CFree(translateVar(v), block.get.sz)
      case Call(v, args, _) =>
        CCall(translateVar(v), args.map(translateExpr))
      case _ =>
        throw TranslationException("Operation not supported")
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

    def updateProducerPost(nextItems: Seq[CertTree.Node], nextKont: CStmtProducer): CStmtProducer = nextKont match {
      case _: Branching =>
        nextItems.tail.foldLeft(nextKont >> kont) {
          case (foldedP, item) => FoldCStmtProducer(traverseStmt, item, foldedP)
        }
      case _ =>
        nextKont >> kont
    }

    // generated nested continuations for children
    val p = translateProducer(node.kont).simplify
    val nextItems = node.children
    val nextKont = updateProducerPost(nextItems, p).simplify

    nextItems.headOption match {
      case Some(childHead) =>
        traverseStmt(childHead, nextKont)
      case None =>
        nextKont(Nil)
    }
  }
}
