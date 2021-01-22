package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.language.Expressions.CVar
import org.tygus.suslik.certification.targets.htt.program.Statements._

object ProgramTranslation {
  def translate(ir: IR.Node): CStatement = irToProgramStatements(ir)

  def irToProgramStatements(node: IR.Node): CStatement = {
    def visit(node: IR.Node): CStatement = node match {
      case IR.EmpRule(_) => CSkip
      case IR.Call(stmt, next, _) => stmt >> visit(next.head)
      case IR.Free(stmt, next, _) => stmt >> visit(next.head)
      case IR.Malloc(stmt, next, _) => stmt >> visit(next.head)
      case IR.Read(stmt, next, _) => stmt >> visit(next.head)
      case IR.Write(stmt, next, _) => stmt >> visit(next.head)
      case IR.Branch(cond, Seq(tb, eb), _) => CIf(cond, visit(tb), visit(eb))
      case IR.Open(app, clauses, selectors, next, ctx) =>
        val cond_branches = selectors.zip(next.map(visit)).reverse
        val ctail = cond_branches.tail
        val finalBranch = cond_branches.head._2
        ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => CIf(c, tb, eb) }
      case IR.Inconsistency(_) => CSkip
      case _ => visit(node.next.head)
    }
    pruneUnusedReads(visit(node).simplify)
  }

  def pruneUnusedReads(stmts: CStatement): CStatement = {
    def visit(stmt: CStatement): (CStatement, Set[CVar]) = stmt match {
      case CSeqComp(s1, s2) =>
        val (s2New, s2Used) = visit(s2)
        val (s1New, s1Used) = visit(s1)
        s1 match {
          case CLoad(to, _, _, _) if !s2Used.contains(to) => (s2New, s2Used)
          case _ => (s1New >> s2New, s1Used ++ s2Used)
        }
      case CIf(cond, tb, eb) =>
        val (tbNew, tbUsed) = visit(tb)
        val (ebNew, ebUsed) = visit(eb)
        (CIf(cond, tbNew, ebNew), tbUsed ++ ebUsed ++ cond.vars)
      case CLoad(to, tpe, from, offset) => (stmt, Set(to, from))
      case CStore(to, offset, e) => (stmt, Set(to) ++ e.vars.toSet)
      case CMalloc(to, tpe, sz) => (stmt, Set(to))
      case CFree(v, sz) => (stmt, Set(v))
      case CCall(fun, args) => (stmt, args.flatMap(_.vars).toSet)
      case _ => (stmt, Set.empty)
    }
    visit(stmts)._1
  }
}
