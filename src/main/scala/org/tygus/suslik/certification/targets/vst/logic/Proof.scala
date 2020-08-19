package org.tygus.suslik.certification.targets.vst.logic

import com.sun.imageio.plugins.bmp.BMPCompressionTypes
import org.tygus.suslik.certification.targets.vst.clang.Expressions.{CExpr, CVar}
import org.tygus.suslik.certification.targets.vst.clang.{CTypes, Expressions, PrettyPrinting}
import org.tygus.suslik.certification.targets.vst.clang.CTypes.VSTCType
import org.tygus.suslik.certification.targets.vst.logic.Formulae.VSTHeaplet
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.VSTProofType
import org.tygus.suslik.language.Ident

object Proof {

  sealed abstract class PureFormula extends PrettyPrinting

  /** predicate encoding that C-parameter (of type val) is a valid pointer */
  case class IsValidPointerOrNull(name: CVar) extends PureFormula {
    override def pp: String =
      s"is_valid_pointer_or_null(${name.pp})"
  }

  /** predicate encoding that C-parameter (of type val) is a valid int */
  case class IsValidInt(name: CVar) extends PureFormula {
    override def pp:String =
      s"ssl_is_valid_int(s${name})"
  }

  /** Redefinition of expressions for use in VST proofs
    *  */
  object Expressions {
    sealed abstract class ProofCExpr extends PrettyPrinting {
      /** prints the expression as though it were an element
        * of type val (vst's encoding of C-values)
        */
      def pp_as_c_value : String = this match {
        case ProofCVar(name, typ) => typ match {
          case ProofTypes.CoqParamType(ty) => name
          case ProofTypes.CoqPtrType => name
          case ProofTypes.CoqIntType => s"(Vint (Int.repr ${name}))"
          case ProofTypes.CoqNatType => s"(Vint (Int.repr (Z.of_nat ${name})))"
          case ProofTypes.CoqListType(elem, length) => name
        }
        case ProofCIntConst(value) => s"(Vint (Int.repr ${value.toString}))"
        case ProofCSetLiteral(elems) =>
          s"[${elems.map(_.pp_as_c_value).mkString("; ")}]"
        case value@ProofCBinaryExpr(op, _, _) =>
          val is_int = op match {
            case ProofCOpPlus => true
            case ProofCOpMinus =>true
            case ProofCOpMultiply =>true
            case _ => false
          }
          if (is_int) {
            s"(Vint (Int.repr ${value.pp}))"
          } else {
            value.pp
          }
        case value@ProofCUnaryExpr(op, _) => op match {
          case ProofCOpNot => value.pp
          case ProofCOpUnaryMinus => s"(Vint (Int.repr ${value.pp}))"
        }
        case v => v.pp
      }
    }

    /** a variable in a VST proof */
    case class ProofCVar(name: String, typ: VSTProofType) extends ProofCExpr {
      override def pp: String = typ match {
        case ProofTypes.CoqPtrType => name
        case ProofTypes.CoqIntType => name
        case ProofTypes.CoqNatType => name
        case ProofTypes.CoqParamType(ty) =>
          // if the variable has a param type then
          // its actually of type val, and we need to
          // extract it's contained value
          ty match {
            case CTypes.CIntType => s"(force_signed_int ${name})"
            case CTypes.CVoidPtrType => s"${name}"
            case CTypes.CUnitType => ??? /// Unimplemented as we should never be dealing with unit types
          }
        case ProofTypes.CoqListType(elem, _) => name
      }
    }

    /** boolean constant in a VST proof */
    case class ProofCBoolConst(value: Boolean) extends ProofCExpr {
      override def pp: String = value.toString
    }

    /** integer constant in a VST proof */
    case class ProofCIntConst(value: Int) extends ProofCExpr {
      override def pp: String = value.toString
    }

    /** set literal (encoded as set) in a VST proof */
    case class ProofCSetLiteral(elems: List[ProofCExpr]) extends ProofCExpr {
      override def pp: String =
        s"[${elems.map(_.pp).mkString("; ")}]"
    }

    /** encodes a ternary expression in a VST proof */
    case class ProofCIfThenElse(cond: ProofCExpr, left: ProofCExpr, right: ProofCExpr) extends ProofCExpr {
      override def pp: String =
        s"(if ${cond.pp} then ${left.pp} else ${right.pp})"
    }

    case class ProofCBinaryExpr(op: ProofCBinOp, left: ProofCExpr, right: ProofCExpr) extends ProofCExpr {
      override def pp: String =
        op match {
          case ProofCOpLt => s"(${left.pp} < ${right.pp})"
          case ProofCOpLeq => s"(${left.pp} <= ${right.pp})"
          case ProofCOpOr => s"(orb ${left.pp} ${right.pp})"
          case ProofCOpAnd => s"(andb ${left.pp} ${right.pp})"
          case ProofCOpPlus => s"(${left.pp} + ${right.pp})"
          case ProofCOpMinus => s"(${left.pp} - ${right.pp})"
          case ProofCOpMultiply => s"(${left.pp} * ${right.pp})"
          case ProofCOpIntEq => s"(Zeq_bool ${left.pp} ${right.pp})"
          case ProofCOpBoolEq => s"(eqb ${left.pp} ${right.pp})"

          // case ProofCOpSetEq => s"(eqb_list _ ${left.pp} ${right.pp})"
        }
    }

    case class ProofCUnaryExpr(op: ProofCUnOp, e: ProofCExpr) extends ProofCExpr {
      override def pp: String =
        op match {
          case ProofCOpNot => s"(negb ${e.pp})"
          case ProofCOpUnaryMinus => s"(-(${e.pp}))"
        }
    }

    sealed abstract class ProofCUnOp

    object ProofCOpNot extends ProofCUnOp

    object ProofCOpUnaryMinus extends ProofCUnOp

    sealed abstract class ProofCBinOp

    object ProofCOpImplication extends ProofCBinOp
    object ProofCOpPlus extends ProofCBinOp

    object ProofCOpMinus extends ProofCBinOp

    object ProofCOpMultiply extends ProofCBinOp

    object ProofCOpIntEq extends ProofCBinOp

    object ProofCOpBoolEq extends ProofCBinOp

    object ProofCOpSetEq extends ProofCBinOp

    object ProofCOpLeq extends ProofCBinOp

    object ProofCOpLt extends ProofCBinOp

    object ProofCOpAnd extends ProofCBinOp

    object ProofCOpOr extends ProofCBinOp

    object ProofCOpIn extends ProofCBinOp

    object ProofCOpSubset extends ProofCBinOp

    object ProofCOpUnion extends ProofCBinOp
    object ProofCOpDiff extends ProofCBinOp
    object ProofCOpIntersect extends ProofCBinOp

  }

  /** prop predicate encoding that a given propositional expression is true
    *  */
  case class IsTrueProp(expr: Expressions.ProofCExpr) extends PureFormula {
    override def pp: String = {
      s"${expr.pp}"
    }
  }

  /** prop predicate encoding that a given boolean expression is true */
  case class IsTrue(expr: Expressions.ProofCExpr) extends PureFormula {
    override def pp: String = {
      s"(is_true ${expr.pp})"
    }
  }


  sealed case class FormalCondition(
                            pure_constraints: List[PureFormula],
                            spatial_constraints: List[VSTHeaplet]
                            )

  /**
    * Type encoding VST-compliant formal specifications of a C Function
    * @param name name of the function
    * @param c_params parameters of the function
    * @param formal_params parameters of the specification
    * @param existensial_params existential params of the function
    * @param precondition precondtion for the function
    * @param postcondition post condition of the function
    * @param return_type return type of the function
    */
  case class FormalSpecification(
                                  name: Ident,
                                  c_params: Seq[(Ident,VSTCType)],
                                  formal_params: Seq[(Ident,VSTProofType)],
                                  existensial_params: Seq[(Ident,VSTProofType)],
                                  precondition: FormalCondition,
                                  postcondition: FormalCondition,
                                  return_type: VSTCType
                                ) extends PrettyPrinting{

    def as_vst_type(var_type: VSTCType) = var_type match {
      case CTypes.CIntType => "tint"
      case CTypes.CUnitType => "tvoid"
      case CTypes.CVoidPtrType => "(tptr tvoid)"
    }

    override def pp: String = {
      val formal_args = formal_params.map({case (var_name, var_type) => s"${var_name}: ${var_type.pp}"})
      val c_args = c_params.map({case (var_name, _) => s"${var_name}: val"})
      val FormalCondition(pre_pure_constraints, pre_spatial_constraints) = precondition
      val FormalCondition(post_pure_constraints, post_spatial_constraints) = postcondition
      s"""Definition ${name}_spec :=
         |  DECLARE _${name}
         |   WITH ${(c_args ++ formal_args).mkString(", ")}
         |   PRE [ ${c_params.map({case (_, var_type) => s"${as_vst_type(var_type)}"}).mkString(", ") } ]
         |   PROP( ${pre_pure_constraints.map(_.pp).mkString("; ")} )
         |   PARAMS(${c_params.map({case (var_name, _) => var_name}).mkString("; ")})
         |   SEP (${pre_spatial_constraints.map(_.pp).mkString("; ")})
         |   POST[ ${as_vst_type(return_type)} ]${existensial_params match {
        case Nil => ""
          case _ =>
            "\n" ++
            existensial_params.map({case (param_name, param_type) => s"|   EX ${param_name}: ${param_type.pp},"}).mkString("\n")
        }}
         |   PROP( ${post_pure_constraints.map(_.pp).mkString("; ")} )
         |   LOCAL()
         |   SEP (${post_spatial_constraints.map(_.pp).mkString("; ")}).
         |""".stripMargin
    }
  }

  case class VSTClause() {

  }
  case class VSTPredicate(
                           predicate_name: Ident,
                           params: Seq[(CVar, org.tygus.suslik.certification.targets.vst.clang.CTypes.VSTCType)],

                         ) {

  }

  case class Proof(params: Seq[CVar]) {
  }

}
