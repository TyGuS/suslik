package org.tygus.suslik.certification.targets.vst.language

import org.tygus.suslik.certification.targets.vst.language.Types.{CBoolType, CIntType, VSTType}
import org.tygus.suslik.language.Expressions.SubstVar

/** Encodes VST specific C expressions */
object Expressions {

  sealed abstract class CExpr extends PrettyPrinting {  }

  /** VST specific Encoding of variables */
  case class CVar(name: String) extends CExpr {
    override def pp: String = s"${name}"
  }

  case class CBoolConst(value: Boolean) extends CExpr {
    override def pp: String = value.toString
  }

  case class CNatConst(value: Int) extends CExpr {
    override def pp: String = value.toString
  }

  case class CSetLiteral(elems: List[CExpr]) extends CExpr {
  }

  case class CIfThenElse(cond: CExpr, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String =
      s"(${cond.pp} ? ${left.pp} : ${right.pp})"
  }

  case class CBinaryExpr(op: CBinOp, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String =
      op match {
        case COpBoolEq => s"(${left.pp} == ${right.pp})"
        case COpEq => s"(${left.pp} == ${right.pp})"
        case COpLt => s"(${left.pp} < ${right.pp})"
        case COpLeq => s"(${left.pp} <= ${right.pp})"
        case COpOr => s"${left.pp} || ${right.pp}"
        case COpAnd => s"${left.pp} && ${right.pp}"
        case COpPlus => s"(${left.pp} + ${right.pp})"
        case COpMinus => s"(${left.pp} - ${right.pp})"
        case COpMultiply => s"(${left.pp} * ${right.pp})"
      }
  }

  case class CUnaryExpr(op: CUnOp, e: CExpr) extends CExpr {
    override def pp: String =
      op match {
        case COpNot => s"!(${e.pp})"
        case COpUnaryMinus => s"-(${e.pp})"
      }
  }

  sealed abstract class CUnOp extends PrettyPrinting

  object COpNot extends CUnOp {
    override def pp: String = "~~"
  }

  object COpUnaryMinus extends CUnOp

  sealed abstract class CBinOp extends PrettyPrinting

  object COpImplication extends CBinOp {
    override def pp: String = "->"
  }

  object COpPlus extends CBinOp {
    override def pp: String = "+"
  }

  object COpMinus extends CBinOp {
    override def pp: String = "-"
  }

  object COpMultiply extends CBinOp {
    override def pp: String = "*"
  }

  object COpEq extends CBinOp {
    override def pp: String = "=="
  }

  object COpBoolEq extends CBinOp {
    override def pp: String = "="
  }

  object COpLeq extends CBinOp {
    override def pp: String = "<="
  }

  object COpLt extends CBinOp {
    override def pp: String = "<"
  }

  object COpAnd extends CBinOp {
    override def pp: String = "/\\"
  }

  object COpOr extends CBinOp {
    override def pp: String = "\\/"
  }

  object COpUnion extends CBinOp {
    override def pp: String = "++"
  }

  object COpDiff extends CBinOp {
    override def pp: String = "--"
  }

  object COpIn extends CBinOp

  object COpSetEq extends CBinOp {
    override def pp: String = "="
  }

  object COpSubset extends CBinOp {
    override def pp: String = "<="
  }

  object COpIntersect extends CBinOp

}
