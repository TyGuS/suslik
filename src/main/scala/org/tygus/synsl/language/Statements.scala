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
          case Store(to, off, e, rest) =>
            val t = if (off <= 0) to.pp else s"(${to.pp} + $off)"
            builder.append(s"*$t = ${e.pp};\n")
            build(rest)
          case Load(to, tpe, from, off, rest) =>
            val f = if (off <= 0) from.pp else s"(${from.pp} + $off)"
            builder.append(s"${tpe.pp} ${to.pp} = *$f;\n")
            build(rest)
          case Alloc(to, tpe, sz, rest) =>
            builder.append(s"${tpe.pp} ${to.pp} = malloc($sz);\n")
            build(rest)
          case Free(v, rest) =>
            builder.append(s"free($v);\n")
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

    // Expression-collector
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(st: Statement): Set[R] = st match {
        case Return(r) => acc ++ r.map(_.collect(p)).getOrElse(Set.empty)
        case Store(to, off, e, rest) =>
          collector(acc ++ to.collect(p) ++ e.collect(p))(rest)
        case Load(to, tpe, from, off, rest) =>
          collector(acc ++ from.collect(p))(rest)
        case Alloc(_, _, _, rest) =>
          collector(acc)(rest)
        case Free(_, rest) =>
          collector(acc)(rest)
        case Call(to, tpe, fun, args, rest) =>
          val acc1: Set[R] = acc ++ to.collect(p) ++
              fun.collect(p) ++ args.flatMap(_.collect(p)).toSet
          collector(acc1)(rest)
        case If(cond, tb, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(tb)
          collector(acc1)(eb)
      }

      collector(Set.empty)(this)
    }

    def usedVars: Set[Var] = collectE(_.isInstanceOf[Var])

  }

  // return [r];
  case class Return(r: Option[Expr]) extends Statement

  // *to.offset = e; rest
  case class Store(to: Var, offset: Int, e: Expr, rest: Statement) extends Statement

  // tpe to = *from; rest
  case class Load(to: Var, tpe: SynslType, from: Var,
                  offset: Int = 0, rest: Statement) extends Statement

  // tpe to = malloc(n); rest
  case class Alloc(to: Var, tpe: SynslType, sz: Int = 1,
                  rest: Statement) extends Statement

  // free(v); rest
  case class Free(v: Var, rest: Statement) extends Statement

  // tpe to = f(args); rest
  case class Call(to: Var, tpe: SynslType, fun: Var, args: Seq[Expr], rest: Statement) extends Statement

  // if (cond) { tb } else { eb }
  case class If(cond: Expr, tb: Statement, eb: Statement) extends Statement

  // A procedure
  case class Procedure(name: String, tp: SynslType, formals: Seq[(SynslType, Var)], body: Statement) {

    def pp: String =
      s"""
         |${tp.pp} $name (${formals.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
         |${body.pp}
         |}
    """.stripMargin

  }

}
