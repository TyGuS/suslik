package org.tygus.suslik.certification.targets.vst.language

import org.tygus.suslik.certification.targets.vst.language.CTypes.{CBoolType, CIntType, VSTCType}
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

  case class CIfThenElse(cond: CExpr, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String =
      s"(${cond.pp} ? ${left.pp} : ${right.pp})"
  }

  case class CBinaryExpr(op: CBinOp, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String =
      op match {
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

  sealed abstract class CUnOp

  object COpNot extends CUnOp
  object COpUnaryMinus extends CUnOp

  sealed abstract class CBinOp

  object COpPlus extends CBinOp

  object COpMinus extends CBinOp

  object COpMultiply extends CBinOp

  object COpEq extends CBinOp

  object COpLeq extends CBinOp

  object COpLt extends CBinOp

  object COpAnd extends CBinOp

  object COpOr extends CBinOp

}
