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
          case Skip => builder.append("skip;\n")
          case Malloc(to, _, sz, rest) =>
            // Ignore type
            builder.append(s"let ${to.pp} = malloc($sz);\n")
            build(rest)
          case Free(v, rest) =>
            builder.append(s"free(${v.pp});\n")
            build(rest)
          case Store(to, off, e, rest) =>
            val t = if (off <= 0) to.pp else s"(${to.pp} + $off)"
            builder.append(s"*$t = ${e.pp};\n")
            build(rest)
          case Load(to, _, from, off, rest) =>
            val f = if (off <= 0) from.pp else s"(${from.pp} + $off)"
            // Do not print the type annotation
            builder.append(s"let ${to.pp} = *$f;\n")
            build(rest)
          case Call(tt, fun, args, rest) =>
            tt match {
              case Some(tpe) =>
                builder.append(s"${tpe._2.pp} ${tpe._1.pp} = " +
                    s"${fun.pp}(${args.map(_.pp).mkString(", ")});\n")
                build(rest)
              case None =>
                builder.append(s"${fun.pp}(${args.map(_.pp).mkString(", ")});\n")
                build(rest)
            }
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
        case Skip => acc
        case Store(to, off, e, rest) =>
          collector(acc ++ to.collect(p) ++ e.collect(p))(rest)
        case Load(_, _, from, off, rest) =>
          collector(acc ++ from.collect(p))(rest)
        case Malloc(_, _, _, rest) =>
          collector(acc)(rest)
        case Free(x, rest) =>
          collector(acc ++ x.collect(p))(rest)
        case Call(_, fun, args, rest) =>
          val acc1: Set[R] = acc ++ fun.collect(p) ++ args.flatMap(_.collect(p)).toSet
          collector(acc1)(rest)
        case If(cond, tb, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(tb)
          collector(acc1)(eb)
      }

      collector(Set.empty)(this)
    }

    def usedVars: Set[Var] = collectE(_.isInstanceOf[Var])

  }

  // skip;
  case object Skip extends Statement

  // let to = malloc(n); rest
  case class Malloc(to: Var, tpe: SynslType, sz: Int = 1,
                    rest: Statement) extends Statement

  // free(v); rest
  case class Free(v: Var, rest: Statement) extends Statement

  // let to = *from; rest
  case class Load(to: Var, tpe: SynslType, from: Var,
                  offset: Int = 0, rest: Statement) extends Statement

  // *to.offset = e; rest
  case class Store(to: Var, offset: Int, e: Expr, rest: Statement) extends Statement

  // f(args); rest
  // or
  // let to = f(args); rest
  case class Call(to: Option[(Var, SynslType)], fun: Var, args: Seq[Expr], rest: Statement) extends Statement

  // if (cond) { tb } else { eb }
  case class If(cond: Expr, tb: Statement, eb: Statement) extends Statement

  // A procedure
  case class Procedure(name: String, tp: SynslType, formals: Seq[(SynslType, Var)], body: Statement) {

    def pp: String =
      s"""
         |${tp.pp} $name (${formals.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
         |${body.pp}}
    """.stripMargin

  }

}
