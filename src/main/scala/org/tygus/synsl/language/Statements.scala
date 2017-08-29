package org.tygus.synsl.language

import org.tygus.synsl.util.StringUtil._

/**
  * @author Ilya Sergey
  */
object Statements {

  import Expressions._

  sealed abstract class Statement {

    // Pretty-printer
    def pp: String = {

      val builder = new StringBuilder

      def build(s: Statement, offset: Int = 2): Unit = {
        builder.append(mkSpaces(offset))
        s match {
          case Return(r) =>
            r match {
              case Some(value) => builder.append(s"return ${value.toString};")
              case None => builder.append("return;")
            }
          case Store(to, e, rest) =>
            builder.append(s"*${to.pp} = ${e.pp};\n")
            build(rest)
          case Load(to, tpe, from, rest) =>
            builder.append(s"${tpe.pp} ${to.pp} = *${from.pp};\n")
            build(rest)
          case Call(to, tpe, fun, args, rest) =>
            builder.append(s"${tpe.pp} ${to.pp} = " +
                s"${fun.pp}(${args.map(_.pp).mkString(", ")});\n")
            build(rest)
          case If(cond, tb, eb) =>
            builder.append(s"if (${cond.pp}) {\n")
            build(tb, offset + 2)
            builder.append(mkSpaces(offset)).append(s"} else {\n")
            build(eb, offset + 2)
            builder.append(mkSpaces(offset)).append(s"}\n")
        }
      }

      build(this)
      builder.toString()
    }

  }

  // return [r];
  case class Return(r: Option[Expr]) extends Statement

  // *to = e; rest
  case class Store(to: Var, e: Expr, rest: Statement) extends Statement

  // tpe to = *from; rest
  case class Load(to: Var, tpe: SynslType, from: Var, rest: Statement) extends Statement

  // tpe to = f(args); rest
  case class Call(to: Var, tpe: SynslType, fun: Var, args: Seq[Expr], rest: Statement) extends Statement

  // if (cond) { tb } else { eb }
  case class If(cond: Expr, tb: Statement, eb: Statement) extends Statement

  // TODO: add allocation/deallocation

  // A procedure
  case class Procedure(name: String, tp: SynslType, formals: Seq[(SynslType, Var)], body: Statement) {

  def pp : String =
    s"""
      |${tp.pp} $name (${formals.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
      |${body.pp}
      |}
    """.stripMargin


  }

}
