package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.targets.vst.clang.CTypes
import org.tygus.suslik.certification.targets.vst.clang.CTypes._
import org.tygus.suslik.certification.targets.vst.clang.Expressions._
import org.tygus.suslik.certification.targets.vst.clang.Statements._
import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.{Procedure, Statement}
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Gamma

/** encapsulates all functions for translating suslik terms to a C encoding */
object CTranslation {

  def translate_unary_expr(e1: UnaryExpr): CExpr = {
    def translate_unary_op : UnOp => CUnOp = {
      case OpNot => COpNot
      case OpUnaryMinus => COpUnaryMinus
    }
    CUnaryExpr(translate_unary_op(e1.op), translate_expression(e1.arg))
  }

  /** translates a variable to C Expression type */
  def translate_variable : Var => CVar = { case Var(name) => CVar(name) }


   /** translates a unary operation to a C expression */
  def translate_binary_op: BinOp => CBinOp = {
    case OpPlus => COpPlus
    case OpMinus => COpMinus
    case OpMultiply => COpMultiply
    case OpEq => COpEq
    case OpLeq => COpLeq
    case OpLt => COpLt
    case OpAnd => COpAnd
    case OpOr => COpOr
    case v => throw TranslationException(s"translation to C program failed - use of unsupported binary operation ${v.pp}")
  }

  def translate_binary_expr(op: BinOp, e1: Expr, e2: Expr): CExpr = {
    CBinaryExpr(translate_binary_op(op), translate_expression(e1), translate_expression(e2))
  }


  def translate_overloaded_binary_expr(expr: OverloadedBinaryExpr): CExpr = expr match {
    case OverloadedBinaryExpr(overloaded_op, left, right) =>
      val tleft = translate_expression(left)
      val tright = translate_expression(right)
      overloaded_op match {
        case op: BinOp => CBinaryExpr(translate_binary_op(op), tleft, tright)
        case OpOverloadedEq => CBinaryExpr(COpEq, tleft, tright)
        case OpNotEqual =>
          CUnaryExpr(COpNot, CBinaryExpr(COpEq, tleft, tright))
        case OpGt =>
          CUnaryExpr(COpNot, CBinaryExpr(COpLeq, tleft, tright))
        case OpGeq =>
          CUnaryExpr(COpNot, CBinaryExpr(COpLt, tleft, tright))
        case OpOverloadedPlus =>
          CBinaryExpr(COpPlus, tleft, tright)
        case OpOverloadedMinus =>
          CBinaryExpr(COpMinus, tleft, tright)
        case OpOverloadedLeq =>
          CBinaryExpr(COpLeq, tleft, tright)
        case OpOverloadedStar => ???
      }
  }

  /** translate a Suslik expression into VST specific encoding */
  def translate_expression(expr: Expr): CExpr = expr match {
    case Var(name) => CVar(name)
    case BoolConst(value) => CBoolConst(value)
    case IntConst(value) => CNatConst(value)
    case LocConst(value) => CNatConst(value)  // TODO: handle ptr type
    case e1@UnaryExpr(_, _) => translate_unary_expr(e1)
    case BinaryExpr(op, e1, e2) => translate_binary_expr(op, e1, e2)
    case IfThenElse(c, t, e) => CIfThenElse(translate_expression(c), translate_expression(t), translate_expression(e))
    case expr@OverloadedBinaryExpr(_, _, _) =>
      translate_overloaded_binary_expr(expr)
    case v => throw TranslationException(s"Operation ${v.toString} not supported")
  }


  /** translate type to C Type */
  def translate_type(lType: SSLType): VSTCType = lType match {
    case IntType => CIntType
    case LocType => CVoidPtrType
    case VoidType => CUnitType
    case v => throw TranslationException(s"translating ${v} not implemeneted")
  }

  def is_supported_c_type: SSLType => Boolean = {
    case IntType => true
    case LocType => true
    case _ => false
  }


  /** translates a suslik encoding of a procedure to a VST C one */
  def translate_function(proc:Procedure, gamma: Gamma) = {
    val ctx: Map[CVar, AnalysisVSTTypes] =
      gamma
        .filter({ case (_, lType) => is_supported_c_type(lType)})
        .map({
          case (variable, ty) =>
            (translate_variable(variable), translate_type(ty).asInstanceOf[AnalysisVSTTypes])})
    def type_expr (ctx: Map[CVar, AnalysisVSTTypes]) (expr: Expr): Option[AnalysisVSTTypes] = {
      def translate_op : BinOp => Option[AnalysisVSTTypes] =  {
        case op: RelOp => op match {
          case Expressions.OpEq => Some(CIntType)
          case _ => throw TranslationException(s"Found incompatible expression in body ${expr.pp}")
        }
        case Expressions.OpPlus => Some(CIntType)
        case Expressions.OpMinus => Some(CIntType)
        case Expressions.OpMultiply => Some(CIntType)
        case _ => throw TranslationException(s"Found incompatible expression in body ${expr.pp}")
      }
      expr match {
        case Var(name) => ctx.get(CVar(name))
        case const: Const => const match {
          case IntConst(value) => Some (CIntType)
          case BoolConst(value) => throw TranslationException(s"Found incompatible expression in body ${expr.pp}")
        }
        case BinaryExpr(op, left, right) => translate_op(op)
        case OverloadedBinaryExpr(overloaded_op, left, right) =>
          overloaded_op match {
            case op: BinOp => translate_op(op)
            case Expressions.OpOverloadedPlus => Some(CIntType)
            case Expressions.OpOverloadedMinus => Some(CIntType)
            case _ => throw TranslationException(s"Found incompatible expression in body ${expr.pp}")
          }
        case UnaryExpr(op, arg) => op match {
          case Expressions.OpUnaryMinus => Some(CIntType)
          case _ => throw TranslationException(s"Found incompatible expression in body ${expr.pp}")
        }
        case _ => throw TranslationException(s"Found incompatible expression in body ${expr.pp}")
        case IfThenElse(cond, left, right) => type_expr(ctx)(left).orElse( type_expr(ctx)(right))
      }
    }

    def translate_body(ctx: Map[CVar, AnalysisVSTTypes], body: Statement) : (Map[CVar, AnalysisVSTTypes], CStatement) =
      body match {
        case Statements.Skip => (ctx, CSkip)
        case Statements.Malloc(to, tpe, sz) =>
          (ctx, CMalloc(translate_variable(to), translate_type(tpe), sz))
        case Statements.Free(v) => (ctx, CFree(translate_variable(v)))
        case Statements.Load(to, tpe, from, offset) =>
          val (new_ctx, elem_typ)  = ctx.get(translate_variable(to)) match {
            case Some(value) => (ctx, value.downcast)
            case None => ctx.get(translate_variable(from)) match {
              case Some(CIntPtrType) => (ctx.updated(translate_variable(to), CIntType), CIntType)
              case Some(CVoidPtrPtrType) =>
                (ctx.updated(translate_variable(to), CVoidPtrType), CVoidPtrType)
              // TODO: Handle errors
              case Some(CVoidPtrType) =>
                val new_ctx =
                  ctx.updated(translate_variable(to), CVoidPtrType)
                                    .updated(translate_variable(from), CVoidPtrPtrType)
                (new_ctx, CVoidPtrType)
              case None => ???
            }
          }
          (new_ctx, CLoad(translate_variable(to), elem_typ.downcast, translate_variable(from)))
        case Statements.Store(to, offset, e) =>
          val (new_ctx, elem_ty) =
            type_expr(ctx)(e) match {
              case Some(value) => (ctx.updated(translate_variable(to), value match {
                case cType: VSTCType => cType match {
                  case CTypes.CIntType => CIntPtrType
                  case CTypes.CVoidPtrType => CVoidPtrPtrType
                  case CTypes.CUnitType => ???
                }
                case ptrType: PtrType => ptrType match {
                  case CTypes.CVoidPtrPtrType => CVoidPtrPtrType
                  case CTypes.CIntPtrType => CVoidPtrPtrType
                }
              }), value)
              case None => ctx.get(translate_variable(to)) match {
                  case Some(value) => value match {
                    case ptrType: PtrType => ptrType match {
                      case CTypes.CVoidPtrPtrType => (ctx, CVoidPtrType)
                      case CTypes.CIntPtrType => (ctx, CIntType)
                    }
                    case _ => ???
                  }
                  case None => ???
                }

            }
            (new_ctx, CStore(translate_variable(to),  elem_ty.downcast, offset, translate_expression(e)))
        case Statements.Call(fun, args, companion) =>
          (ctx, CCall(translate_variable(fun), args.map(translate_expression(_)), companion))
        case Statements.SeqComp(s1, s2) =>
          val (new_ctx, s1_up) = translate_body(ctx, s1)
          val (new_ctx2, s2_up) = translate_body(new_ctx, s2)
          (new_ctx2, CSeqComp(s1_up, s2_up))
        case Statements.If(cond, s1, s2) =>
          val (new_ctx, s1_up) = translate_body(ctx, s1)
          val (new_ctx2, s2_up) = translate_body(new_ctx, s2)
          (new_ctx2, CIf(translate_expression(cond), s1_up, s2_up))
        case Statements.Guarded(cond, s1, s2, branchPoint) =>
          val (new_ctx, s1_up) = translate_body(ctx, s1)
          val (new_ctx2, s2_up) = translate_body(new_ctx, s2)
          (new_ctx2, CIf(translate_expression(cond), s1_up, s2_up))
        case Statements.Hole => throw TranslationException(s"Unsupported value ${body.pp} found during translation")
        case Statements.Error => throw TranslationException(s"Unsupported value ${body.pp} found during translation")
      }
    val (_, body) = translate_body(ctx, proc.body)
    CProcedureDefinition(
      proc.f.name,
      translate_type(proc.f.rType),
      proc.f.params.map({ case (variable, rtype) => (translate_variable(variable), translate_type(rtype)) }),
      body
    )
  }


}
