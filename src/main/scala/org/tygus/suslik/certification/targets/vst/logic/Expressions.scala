package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.Types
import org.tygus.suslik.certification.targets.vst.Types.{CoqCardType, CoqIntSetType, CoqIntValType, CoqPtrValType, CoqZType, VSTCType, VSTType}
import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.language.PrettyPrinting


/** Redefinition of expressions for use in VST proofs
  * */
object Expressions {

  sealed trait CLangOp {}
  sealed trait CLangExpr {
    def type_cexpr : VSTCType = this match {
      case ProofCVar(name, typ) => typ.asInstanceOf[VSTCType]
      case ProofCBoolConst(value) => throw TranslationException("Attempted to type a boolean expression")
      case ProofCNullval => CoqPtrValType
      case ProofCIntConst(value) => CoqIntValType
      case ProofCIfThenElse(cond, left : CLangExpr, right : CLangExpr) => left.type_cexpr
      case ProofCBinaryExpr(op : CLangOp, left : CLangExpr, right : CLangExpr) =>
        op match {
          case ProofCOpPlus => CoqIntValType
          case ProofCOpMinus => CoqIntValType
          case ProofCOpMultiply => CoqIntValType
          case ProofCOpZEq | ProofCOpIntValEq | ProofCOpPtrValEq | ProofCOpBoolEq
               | ProofCOpLeq | ProofCOpLt | ProofCOpAnd | ProofCOpOr =>
            throw TranslationException("Attempted to type a boolean expression")
        }
      case ProofCUnaryExpr(op : CLangOp, e : CLangExpr) =>
        op match {
          case ProofCOpNot =>  throw TranslationException("Attempted to type a boolean expression")
          case ProofCOpUnaryMinus => CoqIntValType
        }
    }
    def pp_as_clang_expr: String = this match {
      case ProofCVar(name, typ) => name
      case ProofCBoolConst(value) => value.toString
      case ProofCNullval => "NULL"
      case ProofCIntConst(value) =>value.toString
      case ProofCIfThenElse(cond : CLangExpr, left : CLangExpr, right : CLangExpr) =>
        s"(${cond.pp_as_clang_expr} ? ${left.pp_as_clang_expr} : ${right.pp_as_clang_expr})"
      case ProofCBinaryExpr(op : CLangOp, left : CLangExpr, right : CLangExpr) =>
        op match {
          case ProofCOpPlus =>  s"(${left.pp_as_clang_expr} + ${right.pp_as_clang_expr})"
          case ProofCOpMinus => s"(${left.pp_as_clang_expr} - ${right.pp_as_clang_expr})"
          case ProofCOpMultiply => s"(${left.pp_as_clang_expr} * ${right.pp_as_clang_expr})"
          case ProofCOpZEq => s"(${left.pp_as_clang_expr} == ${right.pp_as_clang_expr})"
          case ProofCOpIntValEq => s"(${left.pp_as_clang_expr} == ${right.pp_as_clang_expr})"
          case ProofCOpPtrValEq => s"(${left.pp_as_clang_expr} == ${right.pp_as_clang_expr})"
          case ProofCOpBoolEq => s"(${left.pp_as_clang_expr} == ${right.pp_as_clang_expr})"
          case ProofCOpLeq => s"(${left.pp_as_clang_expr} <= ${right.pp_as_clang_expr})"
          case ProofCOpLt => s"(${left.pp_as_clang_expr} < ${right.pp_as_clang_expr})"
          case ProofCOpAnd => s"(${left.pp_as_clang_expr} && ${right.pp_as_clang_expr})"
          case ProofCOpOr => s"(${left.pp_as_clang_expr} || ${right.pp_as_clang_expr})"
        }
      case ProofCUnaryExpr(op : CLangOp, e : CLangExpr) =>
        op match {
          case ProofCOpNot => s"!(${e.pp_as_clang_expr})"
          case ProofCOpUnaryMinus => s"-(${e.pp_as_clang_expr})"
        }
    }
  }
  /** encoding of expressions in VST proof script
    * By default any boolean value will print to prop
    * use pp_as_bool_value to print as a boolean
    */
  sealed abstract class ProofCExpr extends PrettyPrinting {

    /** Applies a renaming to an expression */
    def rename(mapping: Map[String, String]): ProofCExpr = this match {
      case expr@ProofCVar(name, ty) => mapping.get(name) match {
        case Some(name) => ProofCVar(name, ty)
        case None => expr
      }
      case expr@ProofCBoolConst(_) => expr
      case expr@ProofCIntConst(_) => expr
      case expr@ProofCNullval => expr
      case ProofCIntSetLiteral(elems) =>
        ProofCIntSetLiteral(elems.map(_.rename(mapping)))
      case ProofCIfThenElse(cond, left, right) =>
        ProofCIfThenElse(cond.rename(mapping), left.rename(mapping), right.rename(mapping))
      case ProofCBinaryExpr(op, left, right) =>
        ProofCBinaryExpr(op, left.rename(mapping), right.rename(mapping))
      case ProofCUnaryExpr(op, e) =>
        ProofCUnaryExpr(op, e.rename(mapping))
      case ProofCCardinalityConstructor(pred_type, name, args) =>
        ProofCCardinalityConstructor(pred_type, name, args.map(_.rename(mapping)))
    }

    def variables : List[ProofCVar] = this match {
      case ProofCCardinalityConstructor(pred_type, name, args) =>  args.flatMap(_.variables)
      case expr@ProofCVar(name, typ) => List(expr)
      case ProofCBoolConst(value) => List()
      case ProofCNullval => List()
      case ProofCIntConst(value) => List()
      case ProofCIntSetLiteral(elems) => elems.flatMap(_.variables)
      case ProofCIfThenElse(cond, left, right) => cond.variables ++ left.variables ++ right.variables
      case ProofCBinaryExpr(op, left, right) => left.variables ++ right.variables
      case ProofCUnaryExpr(op, e) => e.variables
    }

    /** Applies a substitution to an expression */
    def subst(mapping: Map[String, ProofCExpr]): ProofCExpr = this match {
      case expr@ProofCVar(name, _) => mapping.get(name) match {
        case Some(ProofCVar(o_name, _)) if name == o_name => expr
        // avoid infinite recursion by refusing to subst on expressions that contain the name they were just subst'd with
        case Some(value) if !value.variables.map(_.name).contains(name) => value.subst(mapping)
        case Some(value) => value
        case None => expr
      }
      case expr@ProofCNullval => expr
      case expr@ProofCBoolConst(_) => expr
      case expr@ProofCIntConst(_) => expr
      case ProofCIntSetLiteral(elems) =>
        ProofCIntSetLiteral(elems.map(_.subst(mapping)))
      case ProofCIfThenElse(cond, left, right) =>
        ProofCIfThenElse(cond.subst(mapping), left.subst(mapping), right.subst(mapping))
      case ProofCBinaryExpr(op, left, right) =>
        ProofCBinaryExpr(op, left.subst(mapping), right.subst(mapping))
      case ProofCUnaryExpr(op, e) =>
        ProofCUnaryExpr(op, e.subst(mapping))
      case ProofCCardinalityConstructor(pred_type, name, args) =>
        ProofCCardinalityConstructor(pred_type, name, args.map(_.subst(mapping)))
    }

    def type_expr: VSTType = this match {
      case ProofCVar(name, typ) => typ
      case ProofCBoolConst(value) => throw new TranslationException("Attempted to type a boolean constant")
      case ProofCIntConst(value) => CoqZType
      case ProofCNullval => CoqPtrValType
      case ProofCIntSetLiteral(elems) => CoqIntSetType
      case ProofCIfThenElse(cond, left, right) => left.type_expr
      case ProofCBinaryExpr(op, left, right) => op match {
        case ProofCOpUnion | ProofCOpDiff | ProofCOpIntersect => CoqIntSetType
        case ProofCOpPlus | ProofCOpMinus | ProofCOpMultiply => CoqZType
        case ProofCOpImplication | ProofCOpSubset
             | ProofCOpZEq | ProofCOpIntValEq | ProofCOpPtrValEq
             | ProofCOpBoolEq | ProofCOpSetEq | ProofCOpLeq
             | ProofCOpLt | ProofCOpAnd | ProofCOpOr | ProofCOpIn =>
          throw TranslationException(s"Attempted to type a comparison")
      }
      case ProofCUnaryExpr(op, e) => e.type_expr
      case ProofCCardinalityConstructor(pred_type, _, _) => CoqCardType(pred_type)
    }

    /** prints the expression as though it were an element
      * of type val (vst's encoding of C-values)
      */
    def pp_as_c_value: String = this match {
      case ProofCVar(name, typ) => typ match {
        case CoqPtrValType => s"(${name} : val)"
        case CoqIntValType => s"(${name} : val)"
        case CoqZType => s"((Vint (Int.repr ${name})) : val)"
        case _ => throw TranslationException(s"Attempt to print incompatible type ${typ.pp} as a term of type val")
      }
      case ProofCIntConst(value) => s"((Vint (Int.repr ${value.toString})) : val)"
      case v => v.type_expr match {
        case Types.CoqPtrValType => v.pp
        case Types.CoqIntValType => v.pp
        case Types.CoqZType => s"((Vint (Int.repr (${v.pp}))) : val)"
        case v => throw TranslationException(s"Attempt to print incompatible value ${v.pp} as term of type val")
      }
    }

    def pp_as_ssl_union_value: String = {
      this.type_expr match {
        case Types.CoqPtrValType => s"(inr ${this.pp_as_c_value})"
        case Types.CoqIntValType => s"(inl ${this.pp_as_c_value})"
        case Types.CoqZType => s"(inl ${this.pp_as_c_value})"
        case _ => throw TranslationException(s"Attempt to print incompatible value ${this.pp} as a term of type val")
      }
    }

    def pp_as_bool_value: String = this match {
      case value@ProofCBinaryExpr(op, expr_a, expr_b) =>
        op match {
          case ProofCOpImplication => s"(implb ${expr_a.pp_as_bool_value} ${expr_b.pp_as_bool_value})"
          case ProofCOpZEq => s"(Nat.eqb ${expr_a.pp} ${expr_b.pp})"
          case ProofCOpBoolEq => s"(eqb ${expr_a.pp} ${expr_b.pp})"
          case ProofCOpLeq => s"(Z.leb ${expr_a.pp} ${expr_b.pp})"
          case ProofCOpLt => s"(Z.ltb ${expr_a.pp} ${expr_b.pp})"
          case ProofCOpAnd => s"(andb ${expr_a.pp_as_bool_value} ${expr_b.pp_as_bool_value})"
          case ProofCOpOr => s"(orb ${expr_a.pp_as_bool_value} ${expr_b.pp_as_bool_value})"
          case ProofCOpSetEq => s"(perm_eq ${expr_a.pp} ${expr_b.pp})"
          case _ => throw TranslationException(s"Attempted to print invalid expression ${this.pp} as bool value.")
        }
      case value@ProofCUnaryExpr(op, _) => op match {
        case ProofCOpNot => value.pp
        case _ => throw TranslationException(s"Attempted to print invalid expression ${this.pp} as bool value.")
      }
      case _ => throw TranslationException(s"Attempted to print invalid expression ${this.pp} as bool value.")
    }

    def pp_as_Z_value: String =
      this.type_expr match {
        case cType: Types.VSTCType =>
          cType match {
            case Types.CoqPtrValType =>
              throw TranslationException(s"Attempted to print invalid expression ${this.pp} as a Z value.")
            case Types.CoqIntValType => s"(force_signed_int ${this.pp})"
          }
        case Types.CoqZType => this.pp
        case _ => throw TranslationException(s"Attempted to print invalid expression ${this.pp} as a Z value.")
      }
  }

  case class ProofCCardinalityConstructor(pred_type: String, name: String, args: List[ProofCExpr]) extends ProofCExpr {
    override def pp: String = s"(${name} ${args.map(_.pp).mkString(" ")} : ${pred_type}_card)"
  }

  /** a variable in a VST proof */
  case class ProofCVar(name: String, typ: VSTType) extends ProofCExpr with CLangExpr {
    override def pp: String = typ match {
      case CoqPtrValType => s"(${name} : val)"
      case CoqIntValType => s"(${name} : val)"
      case CoqZType => s"(${name} : Z)"
      case CoqCardType(ty) => s"(${name} : ${ty}_card)"
      case CoqIntSetType => s"(${name} : list Z)"
    }
  }

  /** boolean constant in a VST proof */
  case class ProofCBoolConst(value: Boolean) extends ProofCExpr with CLangExpr {
    override def pp: String = s"(is_true ${value.toString})"
  }

  /** integer constant in a VST proof */
  case object ProofCNullval extends ProofCExpr with CLangExpr {
    override def pp: String = "nullval"
  }

  /** integer constant in a VST proof */
  case class ProofCIntConst(value: Int) extends ProofCExpr with CLangExpr {
    override def pp: String =
      value.toString
  }

  /** set literal (encoded as set) in a VST proof */
  case class ProofCIntSetLiteral(elems: List[ProofCExpr]) extends ProofCExpr {
    override def pp: String =
      s"([${elems.map(_.pp_as_Z_value).mkString("; ")}] : list Z)"
  }

  /** encodes a ternary expression in a VST proof */
  case class ProofCIfThenElse(cond: ProofCExpr, left: ProofCExpr, right: ProofCExpr) extends ProofCExpr with CLangExpr {
    override def pp: String = s"(if ${cond.pp_as_bool_value} then ${left.pp} else ${right.pp})"
  }

  case class ProofCBinaryExpr(op: ProofCBinOp, left: ProofCExpr, right: ProofCExpr) extends ProofCExpr with CLangExpr {
    override def pp: String =
      op match {
        case ProofCOpLt => s"(${left.pp_as_Z_value} < ${right.pp_as_Z_value})"
        case ProofCOpLeq => s"(${left.pp_as_Z_value} <= ${right.pp_as_Z_value})"
        case ProofCOpOr => s"(${left.pp} \\/ ${right.pp})"
        case ProofCOpAnd => s"(${left.pp} /\\ ${right.pp})"
        case ProofCOpPlus => s"(${left.pp} + ${right.pp})"
        case ProofCOpMinus => s"(${left.pp} - ${right.pp})"
        case ProofCOpMultiply => s"(${left.pp} * ${right.pp})"
        case ProofCOpZEq => s"(${left.pp} = ${right.pp})"
        case ProofCOpBoolEq => s"(${left.pp} = ${right.pp})"
        case ProofCOpPtrValEq => s"(${left.pp} = ${right.pp})"
        case ProofCOpSetEq => s"(${left.pp} = ${right.pp})"
        case ProofCOpUnion => s"(${left.pp} ++ ${right.pp})"
        // case ProofCOpSetEq => s"(eqb_list _ ${left.pp} ${right.pp})"
      }
  }

  case class ProofCUnaryExpr(op: ProofCUnOp, e: ProofCExpr) extends ProofCExpr with CLangExpr {
    override def pp: String =
      op match {
        case ProofCOpNot => s"(~ ${e.pp})"
        case ProofCOpUnaryMinus => s"(-(${e.pp}))"
      }
  }

  sealed abstract class ProofCUnOp

  object ProofCOpNot extends ProofCUnOp with CLangOp

  object ProofCOpUnaryMinus extends ProofCUnOp with CLangOp

  sealed abstract class ProofCBinOp

  object ProofCOpImplication extends ProofCBinOp

  object ProofCOpPlus extends ProofCBinOp with CLangOp

  object ProofCOpMinus extends ProofCBinOp with CLangOp

  object ProofCOpMultiply extends ProofCBinOp with CLangOp

  object ProofCOpZEq extends ProofCBinOp with CLangOp

  object ProofCOpIntValEq extends ProofCBinOp with CLangOp

  object ProofCOpPtrValEq extends ProofCBinOp with CLangOp

  object ProofCOpBoolEq extends ProofCBinOp with CLangOp

  object ProofCOpSetEq extends ProofCBinOp

  object ProofCOpLeq extends ProofCBinOp with CLangOp

  object ProofCOpLt extends ProofCBinOp with CLangOp

  object ProofCOpAnd extends ProofCBinOp with CLangOp

  object ProofCOpOr extends ProofCBinOp with CLangOp

  object ProofCOpIn extends ProofCBinOp

  object ProofCOpSubset extends ProofCBinOp

  object ProofCOpUnion extends ProofCBinOp

  object ProofCOpDiff extends ProofCBinOp

  object ProofCOpIntersect extends ProofCBinOp

}

