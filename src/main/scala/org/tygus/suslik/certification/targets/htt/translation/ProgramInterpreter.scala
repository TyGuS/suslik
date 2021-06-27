package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.program.Statements.{CFree, CGuarded, CIf, CSkip, CStatement, Noop}
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Interpreter
import org.tygus.suslik.certification.traversal.Interpreter.Result

object ProgramInterpreter extends Interpreter[SuslikProofStep, CStatement, ProgramContext] {
  override def interpret(value: SuslikProofStep, ctx: ProgramContext): Interpreter.Result[CStatement, ProgramContext] = {
    val withNoDeferred = (Nil, None, ctx)
    implicit val env = ctx.env
    value match {
      case SuslikProofStep.Open(_, _, _, selectors) =>
        val stmt = CIf(selectors.map(_.translate))
        val childParams = selectors.map(_ => withNoDeferred)
        Result(List(stmt), childParams)
      case SuslikProofStep.Branch(cond) =>
        val stmt = CGuarded(cond.translate)
        Result(List(stmt), List(withNoDeferred, withNoDeferred))
      case _:SuslikProofStep.EmpRule | _:SuslikProofStep.Inconsistency =>
        Result(List(CSkip), Nil)
      case _ =>
        val stmts = value match {
          case SuslikProofStep.Write(stmt) => List(stmt.translate)
          case SuslikProofStep.Read(_, _, stmt) => List(stmt.translate)
          case SuslikProofStep.Malloc(_, _, stmt) => List(stmt.translate)
          case SuslikProofStep.Free(stmt, sz) =>
            val v = stmt.v.translate
            (0 until sz).map(i => CFree(v, i)).toList
          case SuslikProofStep.Call(_, stmt) => List(stmt.translate)
          case _ => List()
        }
        Result(stmts, List(withNoDeferred))
    }
  }
}
