package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HAllocN, HBinOp, HBinaryExpr, HCall, HExpr, HIfThenElse, HLet, HLitBool, HLitInt, HLitLoc, HLitUnit, HLoad, HOpEq, HOpLe, HOpLt, HOpMinus, HOpMultiply, HOpNot, HOpOffset, HOpPlus, HOpUnaryMinus, HProgVar, HStore, HUnOp, HUnaryExpr}
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HIntType, HLocType, HType}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.HSpecExpr
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.language.Expressions.{BinOp, BinaryExpr, BoolConst, Expr, IfThenElse, IntConst, LocConst, OpBoolEq, OpEq, OpLeq, OpLt, OpMinus, OpMultiply, OpNot, OpPlus, OpUnaryMinus, UnOp, UnaryExpr, Var}
import org.tygus.suslik.language.{IntType, LocType, SSLType, Statements}
import org.tygus.suslik.language.Statements.{Call, Load, Malloc, Store}

trait IrisTranslator[A, B] {
  def translate(value: A): B
}

object IrisTranslator {
  case class TranslatorException(msg: String) extends Exception(msg)

  implicit val binOpTranslator: IrisTranslator[BinOp, HBinOp] = {
    case OpPlus => HOpPlus
    case OpMinus => HOpMinus
    case OpMultiply => HOpMultiply
    case OpEq | OpBoolEq => HOpEq
    case OpLeq => HOpLe
    case OpLt => HOpLt
    case _ => ???
  }

  implicit val paramTranslator: IrisTranslator[(Var, SSLType), HProgVar] = el => el._1.translate

  implicit val unopTranslator: IrisTranslator[UnOp, HUnOp] = {
    case OpNot => HOpNot
    case OpUnaryMinus => HOpUnaryMinus
  }

  implicit val exprTranslator: IrisTranslator[Expr, HExpr] = (expr: Expr) => {
    def visit(expr: Expr): HExpr = expr match {
      case Var(name) => HProgVar(name)
      case IntConst(v) => HLitInt(v)
      case LocConst(v) => HLitLoc(v)
      case BoolConst(v) => HLitBool(v)
      case UnaryExpr(op, arg) => HUnaryExpr(op.translate, visit(arg))
      case BinaryExpr(op, left, right) => HBinaryExpr(op.translate, visit(left), visit(right))
      case IfThenElse(cond, t, f) => HIfThenElse(visit(cond), visit(t), visit(f))
      case _ => ???
    }
    visit(expr)
  }

  implicit val progVarTranslator: IrisTranslator[Var, HProgVar] = pv => HProgVar(pv.name)

  implicit val typeTranslator: IrisTranslator[SSLType, HType] = {
    case IntType => HIntType()
    case LocType => HLocType()
    case _ => ???
  }

  implicit val mallocTranslator: IrisTranslator[Malloc, HStore] =
    stmt => HStore(stmt.to.translate, HAllocN(HLitInt(stmt.sz), HLitUnit()))
  implicit val loadTranslator: IrisTranslator[Load, HLet] =
    stmt => {
      val baseVar = stmt.from.translate
      val fromAddr = if (stmt.offset == 0) baseVar else HBinaryExpr(HOpOffset, baseVar, HLitLoc(stmt.offset))
      HLet(stmt.to.translate, HLoad(fromAddr), HLitUnit())
    }
  implicit val storeTranslator: IrisTranslator[Store, HStore] =
    stmt => {
      val baseVar = stmt.to.translate
      val toAddr = if (stmt.offset == 0) baseVar else HBinaryExpr(HOpOffset, baseVar, HLitLoc(stmt.offset))
      HStore(toAddr, stmt.e.translate)
    }

  implicit val callTranslator: IrisTranslator[Call, HCall] = stmt => HCall(stmt.fun.translate, stmt.args.map(_.translate))



}
