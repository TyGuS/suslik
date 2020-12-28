package org.tygus.suslik.language

import org.tygus.suslik.logic.Specifications.GoalLabel
import org.tygus.suslik.logic.{Formals, FunSpec, Gamma}
import org.tygus.suslik.util.StringUtil._

/**
  * @author Ilya Sergey
  */
object Statements {

  import Expressions._

  sealed abstract class Statement extends HasExpressions[Statement] {

    // Pretty-printer
    def pp: String = {

      val builder = new StringBuilder

      def build(s: Statement, offset: Int = 2): Unit = {
        s match {
          case Skip =>
          case Hole =>
            builder.append(mkSpaces(offset))
            builder.append(s"??\n")
          case Error =>
            builder.append(mkSpaces(offset))
            builder.append(s"error;\n")
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
          case Call(fun, args, _) =>
            builder.append(mkSpaces(offset))
            val function_call = s"${fun.pp}(${args.map(_.pp).mkString(", ")});\n"
            builder.append(function_call)
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
          case Guarded(cond, b, eb, _) =>
            builder.append(mkSpaces(offset))
            builder.append(s"assume (${cond.pp}) {\n")
            build(b, offset + 2)
            builder.append(mkSpaces(offset)).append(s"}\n")
            build(eb, offset + 2)
            builder.append(mkSpaces(offset)).append(s"}\n")
        }
      }

      build(this)
      builder.toString()
    }

    // Expression-collector
    def collect[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(st: Statement): Set[R] = st match {
        case Skip => acc
        case Hole => acc
        case Error => acc
        case Store(to, off, e) =>
          acc ++ to.collect(p) ++ e.collect(p)
        case Load(_, _, from, off) =>
          acc ++ from.collect(p)
        case Malloc(_, _, _) =>
          acc
        case Free(x) =>
          acc ++ x.collect(p)
        case Call(fun, args, _) =>
          acc ++ fun.collect(p) ++ args.flatMap(_.collect(p)).toSet
        case SeqComp(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case If(cond, tb, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(tb)
          collector(acc1)(eb)
        case Guarded(cond, b, eb, _) =>
          val acc1 = collector(acc ++ cond.collect(p))(b)
          collector(acc1)(eb)
      }

      collector(Set.empty)(this)
    }

    override def subst(sigma: Subst): Statement = this match {
      case Store(to, off, e) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        Store(to.subst(sigma).asInstanceOf[Var], off, e.subst(sigma))
      }
      case Load(to, tpe, from, offset) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        assert(!sigma.keySet.contains(from) || sigma(from).isInstanceOf[Var])
        Load(to.subst(sigma).asInstanceOf[Var], tpe, from.subst(sigma).asInstanceOf[Var], offset)
      }
      case Malloc(to, tpe, sz) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        Malloc(to.subst(sigma).asInstanceOf[Var], tpe, sz)
      }
      case Free(x) => {
        assert(!sigma.keySet.contains(x) || sigma(x).isInstanceOf[Var])
        Free(x.subst(sigma).asInstanceOf[Var])
      }
      case Call(fun, args, companion) => Call(fun, args.map(_.subst(sigma)), companion)
      case SeqComp(s1, s2) => SeqComp(s1.subst(sigma), s2.subst(sigma))
      case If(cond, tb, eb) => If(cond.subst(sigma), tb.subst(sigma), eb.subst(sigma))
      case Guarded(cond, b, eb, l) => Guarded(cond.subst(sigma), b.subst(sigma), eb.subst(sigma), l)
      case _ => this
    }

    def mapAtomic(f: Statement => Statement): Statement = this match {
      case SeqComp(s1, s2) => SeqComp(s1.mapAtomic(f), s2.mapAtomic(f))
      case If(cond, tb, eb) => If(cond, tb.mapAtomic(f), eb.mapAtomic(f))
      case Guarded(cond, b, eb, l) => Guarded(cond, b.mapAtomic(f), eb.mapAtomic(f), l)
      case _ => f(this)
    }


    // Statement size in AST nodes
    def size: Int = this match {
      case Skip => 0
      case Hole => 1
      case Error => 1
      case Store(to, off, e) => 1 + to.size + e.size
      case Load(to, _, from, _) => 1 + to.size + from.size
      case Malloc(to, _, _) => 1 + to.size
      case Free(x) => 1 + x.size
      case Call(_, args, _) => 1 + args.map(_.size).sum
      case SeqComp(s1,s2) => s1.size + s2.size
      case If(cond, tb, eb) => 1 + cond.size + tb.size + eb.size
      case Guarded(cond, b, eb, _) => 1 + cond.size + b.size + eb.size
    }

    // All atomic statements (load, store, malloc, free, call) inside this statement
    def atomicStatements: List[Statement] = this match {
      case Skip => List()
      case SeqComp(s1,s2) => s1.atomicStatements ++ s2.atomicStatements
      case If(_, tb, eb) => tb.atomicStatements ++ eb.atomicStatements
      case Guarded(_, b, eb, _) => b.atomicStatements ++ eb.atomicStatements
      case _ => List(this)
    }

    // Companions of all calls inside this statement
    def companions: List[GoalLabel] = atomicStatements.flatMap {
      case Call(_, _, Some(comp)) => List(comp)
      case _ => Nil
    }

    def uncons: (Statement, Statement) = this match {
      case SeqComp(s1, s2) => {
        val (head, tail) = s1.uncons
        tail match {
          case Skip => (head, s2)
          case _ => (head, SeqComp(tail, s2))
        }
      }
      case other => (other, Skip)
    }

    def resolveOverloading(gamma: Gamma): Statement = this match {
      case SeqComp(s1,s2)=> SeqComp(
        s1.resolveOverloading(gamma),
        s2.resolveOverloading(gamma)
      )
      case If(cond, tb, eb) => If(
        cond.resolveOverloading(gamma),
        tb.resolveOverloading(gamma),
        eb.resolveOverloading(gamma)
      )
      case Guarded(cond, body, els, branchPoint) => Guarded(
        cond.resolveOverloading(gamma),
        body.resolveOverloading(gamma),
        els.resolveOverloading(gamma),
        branchPoint
      )
      case cmd:Store => cmd.copy(e = cmd.e.resolveOverloading(gamma))
      case cmd:Call => cmd.copy(args = cmd.args.map({e => e.resolveOverloading(gamma)}))
      case other => other
    }

  }

  // skip
  case object Skip extends Statement

  // ??
  case object Hole extends Statement

  // assert false
  case object Error extends Statement

  // let to = malloc(n)
  case class Malloc(to: Var, tpe: SSLType, sz: Int = 1) extends Statement

  // free(v)
  case class Free(v: Var) extends Statement

  // let to = *from.offset
  case class Load(to: Var, tpe: SSLType, from: Var,
                  offset: Int = 0) extends Statement

  // *to.offset = e
  case class Store(to: Var, offset: Int, e: Expr) extends Statement

  // f(args)
  case class Call(fun: Var, args: Seq[Expr], companion: Option[GoalLabel]) extends Statement

  // s1; s2
  case class SeqComp(s1: Statement, s2: Statement) extends Statement {
    def simplify: Statement = {
      (s1, s2) match {
        case (Guarded(cond, b, eb, l), _) => Guarded(cond, SeqComp(b, s2).simplify, eb, l) // Guards are propagated to the top
        case (_, Guarded(cond, b, eb, l)) => Guarded(cond, SeqComp(s1, b).simplify, eb, l) // Guards are propagated to the top
        case (Load(y, tpe, from, offset), _) => simplifyBinding(y, newY => Load(newY, tpe, from, offset))
        case (Malloc(to, tpe, sz), _) => simplifyBinding(to, newTo => Malloc(newTo, tpe, sz))
        case _ => this
      }
    }

    // Eliminate or shorten newly bound variable newvar
    // depending on the rest of the program (s2)
    private def simplifyBinding(newvar: Var, mkBinding: Var => Statement): Statement = {
      val used = s2.vars
      if (used.contains(newvar)) {
        // Try to shorten the variable name
        val prefixes = Range(1, newvar.name.length).map(n => newvar.name.take(n))
        prefixes.find(p => !used.contains(Var(p))) match {
          case None => this // All shorter names are used
          case Some(name) => SeqComp(mkBinding(Var(name)), s2.subst(newvar, Var(name)))
        }
      } else s2 // Do not generate bindings for unused variables
    }
  }

  // if (cond) { tb } else { eb }
  case class If(cond: Expr, tb: Statement, eb: Statement) extends Statement {
    def simplify: Statement = {
      (tb, eb) match {
        case (Skip, Skip) => Skip
        case (Error, _) => eb
        case (_, Error) => tb
        case (Guarded(gcond, gb, geb, _), _) => If(cond, If(gcond, gb, geb), eb).simplify // TODO: this handles nested branch abductions but it's not particularly sound
        case (_, Guarded(gcond, gb, geb, _)) => If(cond, tb, If(gcond, gb, geb)).simplify
        case _ => this
      }
    }
  }

  // assume cond { body } else { els }
  case class Guarded(cond: Expr, body: Statement, els: Statement, branchPoint: GoalLabel) extends Statement

  // A procedure
  case class Procedure(f: FunSpec, body: Statement) {
    
    val (name: String, tp: SSLType, formals: Formals) = (f.name, f.rType, f.params)

    def pp: String =
      s"""
         |${tp.pp} $name (${formals.map { case (i, t) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
         |${body.pp}}
    """.stripMargin

    def removeUnusedParams(outerCall: Call): (Procedure, Call) = {

      def isRecCall(s: Statement) = s.isInstanceOf[Call] && s.asInstanceOf[Call].fun.name == f.name
      val recCalls = body.atomicStatements.filter(isRecCall).map(_.asInstanceOf[Call])
      val rest = body.mapAtomic(s => if (isRecCall(s)) Skip else s)

      def rmAtIndex(args: Seq[Expr], i: Int): Seq[Expr] = args.take(i) ++ args.drop(i + 1)

      val unusedParams = for {
        param <- f.params
        if !rest.vars.contains(param._1)
        ind = f.params.indexOf(param)
        if recCalls.forall(c => !rmAtIndex(c.args, ind).flatMap(_.vars).contains(param._1))
      } yield (ind, param)

      val unusedArgs = unusedParams.map(_._1)
      def removeUnusedArgs(c:Call): Call = {
        val newArgs = c.args.indices.filterNot(unusedArgs.contains(_)).map(i => c.args(i))
        c.copy(args = newArgs)
      }
      def removeCallArgs(s: Statement): Statement = if (isRecCall(s)) {
        removeUnusedArgs(s.asInstanceOf[Call])
      } else s

      val usedParams = f.params.filterNot(p => unusedParams.map(_._2).contains(p))
      val newProc = this.copy(f = this.f.copy(params = usedParams), body = this.body.mapAtomic(removeCallArgs))
      val newCall = removeUnusedArgs(outerCall)
      (newProc, newCall)
    }

  }

  // Solution for a synthesis goal:
  // a statement and a possibly empty list of recursive helpers
  type Solution = (Statement, List[Procedure])

}
