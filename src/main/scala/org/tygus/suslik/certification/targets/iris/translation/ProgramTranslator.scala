package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HBinaryExpr, HExpr, HFree, HGuarded, HIf, HLitLoc, HLitUnit, HNoOp, HOpOffset}
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Translator
import org.tygus.suslik.certification.traversal.Translator.Result

/**
  * Extract a HeapLang program directly from the SSL proof.
  */
object ProgramTranslator extends Translator[SuslikProofStep, HExpr, TranslationContext]  {

  override def translate(step: SuslikProofStep, ctx: TranslationContext): Translator.Result[HExpr, TranslationContext] = {
    val withNoDeferred = (Nil, None, ctx)
    step match {
      case SuslikProofStep.Open(_, _, _, selectors) =>
        val stmt = HIf(selectors.map(_.translate))
        val conts = selectors.map(_ => withNoDeferred)
        Result(List(stmt), conts)
      case SuslikProofStep.Branch(cond, _) =>
        val stmt = HGuarded(cond.translate)
        Result(List(stmt), List(withNoDeferred, withNoDeferred))
      case _:SuslikProofStep.EmpRule | _: SuslikProofStep.Inconsistency =>
        Result(List(HLitUnit()), Nil)
      case _ =>
        val stmts = step match {
          case SuslikProofStep.Write(stmt) => List(stmt.translate)
          case SuslikProofStep.Read(_, _, stmt) => List(stmt.translate)
          case SuslikProofStep.Malloc(_, _, stmt) => List(stmt.translate)
          case SuslikProofStep.Free(stmt, sz) =>
            val v = stmt.v.translate
            val addr = (sz: Int) => if (sz == 0) v else HBinaryExpr(HOpOffset, v, HLitLoc(sz))
            (0 until sz).map(i => HFree(addr(i))).toList
          case SuslikProofStep.Call(_, stmt) => List(stmt.translate)
          case _ => List(HNoOp)
        }
        Result(stmts, List(withNoDeferred))
    }
  }

}
