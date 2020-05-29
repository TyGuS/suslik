package org.tygus.suslik.certification.targets.coq.language

import org.tygus.suslik.util.StringUtil._

object Statements {
  import Expressions._

  sealed abstract class CStatement extends ProgramPrettyPrinting {
    // Expression-collector
    def collectE[R <: CExpr](p: CExpr => Boolean): Set[R] = {

      def collector(acc: Set[R])(st: CStatement): Set[R] = st match {
        case CSkip => acc
        case CHole => acc
        case CError => acc
        case CMagic => acc
        case CStore(to, off, e) =>
          acc ++ to.collect(p) ++ e.collect(p)
        case CLoad(_, _, from, off) =>
          acc ++ from.collect(p)
        case CMalloc(_, _, _) =>
          acc
        case CFree(x, _) =>
          acc ++ x.collect(p)
        case CCall(fun, args) =>
          acc ++ fun.collect(p) ++ args.flatMap(_.collect(p)).toSet
        case CSeqComp(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case CIf(cond, tb, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(tb)
          collector(acc1)(eb)
        case CGuarded(cond, b) =>
          collector(acc ++ cond.collect(p))(b)
      }

      collector(Set.empty)(this)
    }

    def usedVars: Set[CVar] = this match {
      case _ => collectE(_.isInstanceOf[CVar])
    }

    override def pp: String = {
      val builder = new StringBuilder

      def build(s: CStatement, offset: Int = 2) : Unit = {
        s match {
          case CSkip =>
            builder.append(mkSpaces(offset))
            builder.append("ret tt")
          case CHole => ???
          case CError => ???
          case CMagic => ???
          case CMalloc(to, _, sz) =>
            builder.append(mkSpaces(offset))
            builder.append(s"${to.ppp} <-- allocb ${to.ppp} $sz")
          case CFree(v, off) =>
            builder.append(mkSpaces(offset))
            if (off > 0) {
              builder.append(s"dealloc (${v.ppp} .+ $off)")
            } else {
              builder.append(s"dealloc ${v.ppp}")
            }
          case CStore(to, off, e) =>
            builder.append(mkSpaces(offset))
            val t = if (off <= 0) to.ppp else s"(${to.ppp} .+ $off)"
            builder.append(s"$t ::= ${e.ppp}")
          case CLoad(to, tpe, from, off) =>
            builder.append(mkSpaces(offset))
            val f = if (off <= 0) from.ppp else s"(${from.ppp} .+ $off)"
            builder.append(s"${to.ppp} <-- @read ${tpe.pp} $f")
          case CCall(fun, args) =>
            builder.append(mkSpaces(offset))
            val function_call = s"${fun.ppp} ${args.map(_.ppp).mkString(" ")}"
            // TODO: handle return types
            builder.append(function_call)
          case CSeqComp(s1, s2) =>
            build(s1, offset)
            s1 match {
              case _: ReturnsValue => builder.append(";\n")
              case _ => builder.append(";;\n")
            }
            build(s2, offset)
          case CIf(cond, tb, eb) =>
            builder.append(mkSpaces(offset))
            builder.append(s"if ${cond.ppp}\n")
            builder.append(mkSpaces(offset))
            builder.append(s"then\n")
            build(tb, offset + 2)
            builder.append("\n")
            builder.append(mkSpaces(offset)).append(s"else\n")
            build(eb, offset + 2)
            builder.append("\n")
          case CGuarded(cond, body) => ???
        }
      }

      build(this)
      builder.toString()
    }
  }

  trait ReturnsValue

  case object CSkip extends CStatement

  case object CHole extends CStatement

  case object CError extends CStatement

  case object CMagic extends CStatement

  case class CMalloc(to: CVar, tpe: CoqType, sz: Int = 1) extends CStatement with ReturnsValue

  case class CFree(v: CVar, offset: Int = 0) extends CStatement

  case class CLoad(to: CVar, tpe: CoqType, from: CVar, offset: Int = 0) extends CStatement with ReturnsValue

  case class CStore(to: CVar, offset: Int, e: CExpr) extends CStatement

  case class CCall(fun: CVar, args: Seq[CExpr]) extends CStatement

  case class CIf(cond: CExpr, tb: CStatement, eb: CStatement) extends CStatement {
    def simplify: CStatement = (tb, eb) match {
      case (CSkip, CSkip) => CSkip
      case (CError, _) => eb
      case (_, CError) => tb
      case _ => this
    }
  }

  case class CSeqComp(s1: CStatement, s2: CStatement) extends CStatement {
    def simplify: CStatement = (s1, s2) match {
      case (CGuarded(cond, b), _) => CGuarded(cond, CSeqComp(b, s2).simplify)
      case (CLoad(y, _, _, _), CGuarded(cond, b)) if cond.vars.contains(y) => this
      case (_, CGuarded(cond, b)) => CGuarded(cond, CSeqComp(s1, b).simplify)
      case (CLoad(y, _, _, _), _) => if (s2.usedVars.contains(y)) this else s2 // Do not generate read for unused variables
      case _ => this
    }

  }

  case class CGuarded(cond: CExpr, body: CStatement) extends CStatement

  case class CProcedure(name: String, tp: CoqType, formals: Seq[(CoqType, CVar)], body: CStatement, inductive: Boolean = false) extends CStatement {
    override def pp: String = {
      val builder = new StringBuilder
      builder.append(s"Program Definition $name : ${name}_type :=\n")
      val fvs = formals.map(f => f._2.ppp)
      if (inductive) {
        builder.append(s"  Fix (fun ($name : ${name}_type) ${fvs.mkString(" ")} =>\n")
      } else {
        builder.append(s"  fun ${fvs.mkString(" ")} =>\n")
      }
      builder.append("    Do (\n")
      builder.append(body.ppp)
      builder.append("    )")
      if (inductive) {
        builder.append(")")
      }
      builder.append(".")
      builder.toString()
    }
  }
}
