package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.RelOp
import org.tygus.suslik.language.{BoolType, Expressions, IntSetType, IntType, LocType, SSLType}
import org.tygus.suslik.logic.{PFormula, Specifications}
import org.tygus.suslik.logic.Specifications.Goal

object PureSynthesis {
  def typeToSMT(lType: SSLType): String = lType match {
    case IntType | LocType => "Int"
    case BoolType => "Bool"
    case IntSetType => "(Set Int)"
  }
  val typeConstants: Map[SSLType,List[String]] = Map(
    IntType -> List("0"), LocType -> List("0")
  )

  def toSmtExpr(c: Expressions.Expr, sb: StringBuilder): Unit = c match {
    case Expressions.Var(name) => sb ++= name
    case const: Expressions.Const => sb ++= const.pp
    case Expressions.BinaryExpr(op, left, right) => sb ++= "(" ++= (op match {
      case Expressions.OpAnd => "and"
      case Expressions.OpOr => "or"
      case Expressions.OpImplication => "=>"
      case Expressions.OpPlus => "+"
      case Expressions.OpMinus => "-"
      case Expressions.OpMultiply => "(*"
      case Expressions.OpEq => "="
      case Expressions.OpBoolEq => "="
      case Expressions.OpLeq => "<="
      case Expressions.OpLt => "<"
      //case Expressions.OpIn =>
      //case Expressions.OpSetEq =>
      //case Expressions.OpSubset =>
//      case Expressions.OpUnion =>
//      case Expressions.OpDiff =>
//      case Expressions.OpIntersect =>
    }) ++= " "
      toSmtExpr(left,sb)
      sb ++= " "
      toSmtExpr(right,sb)
      sb ++= ") "
    //case Expressions.OverloadedBinaryExpr(overloaded_op, left, right) =>
    case Expressions.UnaryExpr(op, arg) => sb ++= "(" ++= (op match {
      case Expressions.OpNot => "not"
      case Expressions.OpUnaryMinus => "-"
    }) ++= " "
    toSmtExpr(arg,sb)
      sb ++= ") "
    //case Expressions.SetLiteral(elems) =>
    case Expressions.IfThenElse(cond, left, right) =>
  }

  def toSmt(phi: PFormula, sb: StringBuilder): Unit = phi.conjuncts.size match {
    case 0 => sb ++= "true"
    case 1 => toSmtExpr(phi.conjuncts.head,sb)
    case _ => sb ++= "(and "
              for (c <- phi.conjuncts) toSmtExpr(c,sb)
              sb ++= ")"
  }

  def toSMTTask(goal: Specifications.Goal): String = {
    val sb = new StringBuilder
    sb ++= "(set-logic ALL)\n\n"

    val otherVars = goal.gamma -- goal.existentials
    for(ex <- goal.existentials) {
      val etypeOpt = ex.getType(goal.gamma)
      val etypeStr = typeToSMT(etypeOpt.get)
      sb ++= "(synth-fun target_" ++= ex.name ++= " ("
      for (v <- otherVars)
        sb ++= "(" ++= v._1.name ++= " " ++= typeToSMT(v._2) ++= ") "
      sb ++= ") " ++= etypeStr ++= "\n"
      sb ++= "  ((Start " ++= etypeStr ++= " ("
      for (c <- typeConstants(etypeOpt.get))
        sb ++= c ++= " "
      for (v <- otherVars; if v._2.conformsTo(etypeOpt))
        sb ++= v._1.name ++= " "
      sb ++= ")))"
      sb ++= ")\n"
    }
    sb ++= "\n"
    for (v <- otherVars)
      sb ++= "(declare-var " ++= v._1.name ++= " " ++= typeToSMT(v._2) ++= ")\n"
    sb ++= "\n(constraint\n"
    sb ++= "    (=> "
    toSmt(goal.pre.phi,sb)
    sb ++= " "
    toSmt(goal.post.phi,sb)
    sb ++= "))"
    sb ++= "\n(check-synth)"
    sb.toString
  }
  def apply(goal: Specifications.Goal): Option[Goal] = {

    None
  }

}
