package org.tygus.suslik.certification.targets.htt.program

import org.tygus.suslik.certification.targets.htt.language.PrettyPrinting
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.util.StringUtil.mkSpaces

object Statements {
  sealed abstract class CStatement extends PrettyPrinting {
    // Expression-collector
    def collectE[R <: CExpr](p: CExpr => Boolean): Seq[R] = {

      def collector(acc: Seq[R])(st: CStatement): Seq[R] = st match {
        case CSkip => acc
        case CStore(to, off, e) =>
          acc ++ to.collect(p) ++ e.collect(p)
        case CLoad(_, _, from, off) =>
          acc ++ from.collect(p)
        case CMalloc(_, _, _) =>
          acc
        case CFree(x, _) =>
          acc ++ x.collect(p)
        case CCall(fun, args) =>
          acc ++ fun.collect(p) ++ args.flatMap(_.collect(p))
        case CSeqComp(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case CIf(cond, tb, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(tb)
          collector(acc1)(eb)
        case CGuarded(cond, b, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(b)
          collector(acc1)(eb)
        case _ =>
          acc
      }

      collector(Seq.empty)(this)
    }

    def usedVars: Seq[CVar] = this match {
      case _ => collectE(_.isInstanceOf[CVar])
    }

    override def pp: String = {
      val builder = new StringBuilder

      def build(s: CStatement, depth: Int = 0) : Unit = {
        val indent = getIndent(depth)
        s match {
          case CSkip =>
            builder.append(s"${indent}ret tt")
          case CMalloc(to, _, sz) =>
            builder.append(s"$indent${to.pp} <-- allocb null $sz")
          case CFree(v, sz) =>
            val deallocs = for (off <- 0 until sz) yield {
              if (off > 0) {
                s"dealloc (${v.pp} .+ $off)"
              } else {
                s"dealloc ${v.pp}"
              }
            }
            builder.append(s"$indent${deallocs.mkString(s";;\n${mkSpaces(depth)}")}")
          case CStore(to, off, e) =>
            val t = if (off <= 0) to.pp else s"(${to.pp} .+ $off)"
            val v = if (e == CNatConst(0)) "null" else e.pp
            builder.append(s"$indent$t ::= $v")
          case CLoad(to, tpe, from, off) =>
            val f = if (off <= 0) from.pp else s"(${from.pp} .+ $off)"
            builder.append(s"$indent${to.pp} <-- @read ${tpe.pp} $f")
          case CCall(fun, args) =>
            val function_call = s"$indent${fun.pp} (${args.map(_.pp).mkString(", ")})"
            // TODO: handle return types
            builder.append(function_call)
          case CSeqComp(s1, s2) =>
            build(s1, depth)
            s1 match {
              case _: ReturnsValue => builder.append(";\n")
              case _ => builder.append(";;\n")
            }
            build(s2, depth)
          case CIf(cond, tb, eb) =>
            builder.append(s"${indent}if ${cond.pp}\n")
            builder.append(s"${indent}then\n")
            build(tb, depth + 1)
            builder.append(s"\n${indent}else\n")
            build(eb, depth + 1)
          case CGuarded(cond, body, els) =>
            builder.append(s"${indent}if ${cond.pp}\n")
            builder.append(s"${indent}then\n")
            build(body, depth + 1)
            builder.append(s"\n${indent}else\n")
            build(els, depth + 1)
          case _ =>
        }
      }

      build(this)
      builder.toString()
    }
  }

  trait ReturnsValue

  case object CSkip extends CStatement

  case class CMalloc(to: CVar, tpe: HTTType, sz: Int = 1) extends CStatement with ReturnsValue

  case class CFree(v: CVar, sz: Int = 1) extends CStatement

  case class CLoad(to: CVar, tpe: HTTType, from: CVar, offset: Int = 0) extends CStatement with ReturnsValue

  case class CStore(to: CVar, offset: Int, e: CExpr) extends CStatement

  case class CCall(fun: CVar, args: Seq[CExpr]) extends CStatement

  case class CIf(cond: CExpr, tb: CStatement, eb: CStatement) extends CStatement {
    def simplify: CStatement = (tb, eb) match {
      case (CSkip, CSkip) => CSkip
      case _ => this
    }
  }

  case class CSeqComp(s1: CStatement, s2: CStatement) extends CStatement {
    /**
      * The synthesis removes some extraneous program statements that are unused in the final result, but
      * the CertTree retains them as nodes. So, we remove them from our statements here.
      * @return A simplified statement
      */
    def simplify: CStatement = (s1, s2) match {
      case (CGuarded(cond, b, eb), _) => CGuarded(cond, CSeqComp(b, s2).simplify, eb)
      case (CLoad(y, _, _, _), CGuarded(cond, _, _)) if cond.vars.contains(y) => this
      case (_, CGuarded(cond, b, eb)) => CGuarded(cond, CSeqComp(s1, b).simplify, eb)
      case (CLoad(y, _, _, _), _) => if (s2.usedVars.contains(y)) this else s2 // Do not generate read for unused variables
      case _ => this
    }
  }

  case class CGuarded(cond: CExpr, body: CStatement, els: CStatement) extends CStatement

  case class CProcedure(name: String, tp: HTTType, formals: Seq[(HTTType, CVar)], body: CStatement) extends CStatement {
    override def pp: String = {
      val vprogs = "vprogs"
      val builder = new StringBuilder
      builder.append(s"Program Definition $name : ${name}_type :=\n")
      builder.append(s"${getIndent(1)}Fix (fun ($name : ${name}_type) $vprogs =>\n")

      builder.append(s"${getIndent(2)}let: (${formals.map(_._2.pp).mkString(", ")}) := $vprogs in\n")
      builder.append(s"${getIndent(2)}Do (\n")
      builder.append(body.ppIndent(3))
      builder.append(s"\n${getIndent(2)})).")
      builder.toString()
    }
  }
}
