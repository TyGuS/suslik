package org.tygus.suslik.language

import org.tygus.suslik.logic.Specifications.GoalLabel
import org.tygus.suslik.util.StringUtil._

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
        s match {
          case Skip =>
          case Error =>
            builder.append(mkSpaces(offset))
            builder.append(s"error;\n")
          case Magic =>
            builder.append(mkSpaces(offset))
            builder.append(s"magic;\n")
          case Malloc(to, _, sz) =>
            // Ignore type
            builder.append(mkSpaces(offset))
            builder.append(s"let ${to.pp} = malloc($sz);\n")
          case Free(v) =>
            builder.append(mkSpaces(offset))
            builder.append(s"free(${v.pp});\n")
          case Store(to, off, e) =>
            builder.append(mkSpaces(offset))
            val t = if (off <= 0) to.pp else s"(${to.pp} + $off)"
            builder.append(s"*$t = ${e.pp};\n")
          case Load(to, _, from, off) =>
            builder.append(mkSpaces(offset))
            val f = if (off <= 0) from.pp else s"(${from.pp} + $off)"
            // Do not print the type annotation
            builder.append(s"let ${to.pp} = *$f;\n")
          case Call(tt, fun, args, _) =>
            builder.append(mkSpaces(offset))
            tt match {
              case Some(tpe) =>
                builder.append(s"${tpe._2.pp} ${tpe._1.pp} = " +
                    s"${fun.pp}(${args.map(_.pp).mkString(", ")});\n")
              case None =>
                builder.append(s"${fun.pp}(${args.map(_.pp).mkString(", ")});\n")
            }
          case SeqComp(s1,s2) =>
            build(s1, offset)
            build(s2, offset)
          case If(cond, tb, eb) =>
            builder.append(mkSpaces(offset))
            builder.append(s"if (${cond.pp}) {\n")
            build(tb, offset + 2)
            builder.append(mkSpaces(offset)).append(s"} else {\n")
            build(eb, offset + 2)
            builder.append(mkSpaces(offset)).append(s"}\n")
          case Guarded(cond, b) =>
            builder.append(mkSpaces(offset))
            builder.append(s"assume (${cond.pp}) {\n")
            build(b, offset + 2)
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
        case Error => acc
        case Magic => acc
        case Store(to, off, e) =>
          acc ++ to.collect(p) ++ e.collect(p)
        case Load(_, _, from, off) =>
          acc ++ from.collect(p)
        case Malloc(_, _, _) =>
          acc
        case Free(x) =>
          acc ++ x.collect(p)
        case Call(_, fun, args, _) =>
          acc ++ fun.collect(p) ++ args.flatMap(_.collect(p)).toSet
        case SeqComp(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case If(cond, tb, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(tb)
          collector(acc1)(eb)
        case Guarded(cond, b) =>
          collector(acc ++ cond.collect(p))(b)
      }

      collector(Set.empty)(this)
    }

    def usedVars: Set[Var] = collectE(_.isInstanceOf[Var])

    // Statement size in AST nodes
    def size: Int = this match {
      case Skip => 0
      case Error => 1
      case Magic => 1
      case Store(to, off, e) => 1 + to.size + e.size
      case Load(to, _, from, _) => 1 + to.size + from.size
      case Malloc(to, _, _) => 1 + to.size
      case Free(x) => 1 + x.size
      case Call(_, fun, args, _) => 1 + args.map(_.size).sum
      case SeqComp(s1,s2) => s1.size + s2.size
      case If(cond, tb, eb) => 1 + cond.size + tb.size + eb.size
      case Guarded(cond, b) => 1 + cond.size + b.size
    }

    // Companions of all calls inside this statement
    def companions: List[GoalLabel] = this match {
      case Call(_, _, _, Some(comp)) => List(comp)
      case SeqComp(s1,s2) => s1.companions ++ s2.companions
      case If(_, tb, eb) => tb.companions ++ eb.companions
      case Guarded(_, b) => b.companions
      case _ => Nil
    }
  }

  // skip;
  case object Skip extends Statement

  // assert false;
  case object Error extends Statement

  // assume false;
  case object Magic extends Statement

  // let to = malloc(n); rest
  case class Malloc(to: Var, tpe: SSLType, sz: Int = 1) extends Statement

  // free(v); rest
  case class Free(v: Var) extends Statement

  // let to = *from; rest
  case class Load(to: Var, tpe: SSLType, from: Var,
                  offset: Int = 0) extends Statement

  // *to.offset = e; rest
  case class Store(to: Var, offset: Int, e: Expr) extends Statement

  // f(args); rest
  // or
  // let to = f(args); rest
  case class Call(to: Option[(Var, SSLType)], fun: Var, args: Seq[Expr], companion: Option[GoalLabel]) extends Statement

  case class SeqComp(s1: Statement, s2: Statement) extends Statement {
    def simplify: Statement = {
      (s1, s2) match {
        case (Guarded(cond, b), _) => Guarded(cond, SeqComp(b, s2).simplify)
        case (Load(y, _, _, _), Guarded(cond, b)) if cond.vars.contains(y) => this
        case (_, Guarded(cond, b)) => Guarded(cond, SeqComp(s1, b).simplify)
        case (Load(y, _, _, _), _) => if (s2.usedVars.contains(y)) this else s2 // Do not generate read for unused variables
        case _ => this
      }
    }
  }

  // if (cond) { tb } else { eb }
  case class If(cond: Expr, tb: Statement, eb: Statement) extends Statement {
    def simplify: Statement = {
      (tb, eb) match {
        case (Skip, Skip) => Skip
        case (Error, _) => eb
        case (_, Error) => tb
        case _ => this
      }
    }
  }

  case class Guarded(cond: Expr, body: Statement) extends Statement

  // A procedure
  case class Procedure(name: String, tp: SSLType, formals: Seq[(SSLType, Var)], body: Statement) {

    def pp: String =
      s"""
         |${tp.pp} $name (${formals.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
         |${body.pp}}
    """.stripMargin

  }

  // Solution for a synthesis goal:
  // a statement and a possibly empty list of recursive helpers
  type Solution = (Statement, List[Procedure])

}
