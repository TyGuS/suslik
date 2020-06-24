package org.tygus.suslik.synthesis.rules

import scala.sys.process._
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

  def toSmtExpr(c: Expressions.Expr, existentials: Map[Expressions.Var,String], sb: StringBuilder): Unit = c match {
    case v: Expressions.Var => sb ++= (if (existentials contains v) existentials(v) else v.name)
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
      toSmtExpr(left,existentials,sb)
      sb ++= " "
      toSmtExpr(right,existentials,sb)
      sb ++= ") "
    //case Expressions.OverloadedBinaryExpr(overloaded_op, left, right) =>
    case Expressions.UnaryExpr(op, arg) => sb ++= "(" ++= (op match {
      case Expressions.OpNot => "not"
      case Expressions.OpUnaryMinus => "-"
    }) ++= " "
    toSmtExpr(arg,existentials,sb)
      sb ++= ") "
    //case Expressions.SetLiteral(elems) =>
    case Expressions.IfThenElse(cond, left, right) =>
  }

  def mkExistentialCalls(existentials: Set[Expressions.Var], otherVars: List[(Expressions.Var, SSLType)]): Map[Expressions.Var,String] =
    existentials.map{ex =>
      (ex,  "(target_" + ex.name + (for (v <- otherVars) yield v._1.name).mkString(" ", " ", "") + ")")
    }.toMap

  def toSmt(phi: PFormula, existentials: Map[Expressions.Var,String], sb: StringBuilder): Unit = phi.conjuncts.size match {
    case 0 => sb ++= "true"
    case 1 => toSmtExpr(phi.conjuncts.head,existentials,sb)
    case _ => sb ++= "(and "
              for (c <- phi.conjuncts) toSmtExpr(c,existentials,sb)
              sb ++= ")"
  }

  def toSMTTask(goal: Specifications.Goal): String = {
    val sb = new StringBuilder
    sb ++= "(set-logic ALL)\n\n"

    val otherVars = (goal.gamma -- goal.existentials).toList
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
    lazy val existentialMap = mkExistentialCalls(goal.existentials,otherVars)
    toSmt(goal.pre.phi,existentialMap,sb)
    sb ++= " "
    toSmt(goal.post.phi,existentialMap,sb)
    sb ++= "))"
    sb ++= "\n(check-synth)"
    sb.toString
  }
  val cvc4exe = "C:\\utils\\cvc4\\cvc4-1.7-win64-opt.exe"
  val cvc4Cmd = cvc4exe + " --sygus-out=status-or-def --lang sygus" //" --cegqi-si=all --sygus-out=status-or-def --lang sygus"
  def invokeCVC(task: String): List[String] = { //<-- if we ever get the library compiled, fix it here
    var out: List[String] = null
    val io = BasicIO.standard{ostream =>
      ostream.write(task.getBytes)
      ostream.flush();
      ostream.close()
    }.withOutput{istream =>
      out = scala.io.Source.fromInputStream(istream).getLines().toList
    }
    val cvc4 = cvc4Cmd.run(io)
    if(cvc4.exitValue() != 0) Nil
    else if (out.head == "unknown") Nil //unsynthesizable
    else out
  }
  def apply(goal: Specifications.Goal): Option[Goal] = {
    val smtTask = toSMTTask(goal)

    None
  }

}
