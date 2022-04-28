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
        case Guarded(cond, b) =>
          collector(acc ++ cond.collect(p))(b)
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
      case Guarded(cond, b) => Guarded(cond.subst(sigma), b.subst(sigma))
      case _ => this
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
      case Guarded(cond, b) => 1 + cond.size + b.size
    }

    // Simplified statement: by default do nothing
    def simplify: Statement = this

    // Is this an atomic statement?
    def isAtomic: Boolean = this match {
      case Skip => false
      case If(_,_,_) => false
      case Guarded(_,_) => false
      case SeqComp(_,_) => false
      case _ => true
    }

    // Variables defined by this atomic statement
    def definedVars: Set[Var] = this match {
      case Load(y, _, _, _) => Set(y)
      case Malloc(y, _, _)  => Set (y)
      case _ if !isAtomic => {assert(false, "definedVars called on non-atomic statement"); Set()}
      case _ => Set()
    }

    // All atomic statements (load, store, malloc, free, call) inside this statement
    def atomicStatements: List[Statement] = this match {
      case Skip => List()
      case SeqComp(s1,s2) => s1.atomicStatements ++ s2.atomicStatements
      case If(_, tb, eb) => tb.atomicStatements ++ eb.atomicStatements
      case Guarded(_, b) => b.atomicStatements
      case _ => List(this)
    }

    // Apply f to all atomic statements inside this statement
    def mapAtomic(f: Statement => Statement): Statement = this match {
      case SeqComp(s1, s2) => SeqComp(s1.mapAtomic(f), s2.mapAtomic(f))
      case If(cond, tb, eb) => If(cond, tb.mapAtomic(f), eb.mapAtomic(f))
      case Guarded(cond, b) => Guarded(cond, b.mapAtomic(f))
      case Skip => Skip
      case _ => f(this)
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
      case Guarded(cond, body) => Guarded(
        cond.resolveOverloading(gamma),
        body.resolveOverloading(gamma)
      )
      case cmd:Store => cmd.copy(e = cmd.e.resolveOverloading(gamma))
      case cmd:Call => cmd.copy(args = cmd.args.map({e => e.resolveOverloading(gamma)}))
      case other => other
    }

    // Shorten a variable v to its minimal prefix unused in the current statement.
    def simplifyVariable(v: Var): (Var, Statement) = {
      def pref_len(s: String, t: String): Int = {
        if (s == "" || t == "" || s(0) != t(0)) 0
        else 1 + pref_len(s.substring(1), t.substring(1))
      }
      var min_prefix = 1;
      this.vars.foreach(other => {
        if (other != v) {
          val len = pref_len(v.name, other.name) + 1;
          if (len > min_prefix) min_prefix = len;
        }
      });
      if (min_prefix == v.name.length) (v, this)
      else {
        val new_name = v.name.take(min_prefix);
        (Var(new_name), this.subst(v, Var(new_name)))
      }
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
    override def simplify: Statement = {
      (s1, s2) match {
        case (Skip, _) => s2.simplify // Remove compositions with skip
//        case (_, Skip) => s1.simplify
        case (SeqComp(s11, s12), _) => SeqComp(s11, SeqComp(s12, s2)).simplify // Left-nested compositions are transformed to right-nested
        case (Guarded(_, _), _) => { assert(false, "Guarded statement on LHS of seq comp"); this}
        case (If(_, _, _), _) => { assert(false, "Conditional on LHS of seq comp"); this }
        case (_, Guarded(cond, b)) // Guards are propagated to the top but not beyond the definition of any var in their cond
            if cond.vars.intersect(s1.definedVars).isEmpty => Guarded(cond, SeqComp(s1, b).simplify)
        case (Load(y, tpe, from, offset), _) => simplifyBinding(y, newY => Load(newY, tpe, from, offset))
        case (Malloc(to, tpe, sz), _) => simplifyBinding(to, newTo => Malloc(newTo, tpe, sz))
        case _ => this
      }
    }

    // Eliminate or shorten newly bound variable newvar
    // depending on the rest of the program (s2)
    private def simplifyBinding(newvar: Var, mkBinding: Var => Statement): Statement =
      if (s2.vars.contains(newvar)) {
        val (v, s) = s2.simplifyVariable(newvar)
        SeqComp(mkBinding(v), s)
      } else s2  // Do not generate bindings for unused variables
  }

  // if (cond) { tb } else { eb }
  case class If(cond: Expr, tb: Statement, eb: Statement) extends Statement {
    override def simplify: Statement = {
      (tb, eb) match {
        case (Skip, Skip) => Skip
        case (Error, _) => eb
        case (_, Error) => tb
        case (Guarded(gcond, gb), _) => Guarded(gcond, If(cond, gb, eb).simplify)
        case (_, Guarded(gcond, gb)) => Guarded(gcond, If(cond, tb, gb).simplify)
        case _ => this
      }
    }
  }

  // assume cond { body } else { els }
  case class Guarded(cond: Expr, body: Statement) extends Statement {
    override def simplify: Statement = body match {
      case Guarded(c1, b1) => Guarded(cond && c1, b1)
      case _ => this
    }
  }

  // A procedure
  case class Procedure(f: FunSpec, body: Statement) {
    
    val (name: String, tp: SSLType, formals: Formals) = (f.name, f.rType, f.params)

    def pp: String =
      s"""
         |${tp.pp} $name (${formals.map { case (i, t) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
         |${body.pp}}
    """.stripMargin

    // Shorten parameter names
    def simplifyParams: Procedure = {
      type Acc = (FunSpec, Statement)
      def updateParam(formal: (Var, SSLType), acc: Acc): Acc = {
        val (newParam, newBody) = acc._2.simplifyVariable(formal._1)
        val newSpec = acc._1.varSubst(Map(formal._1 -> newParam))
        (newSpec, newBody)
      }
      val (newSpec, newBody) = f.params.foldRight((f, body))(updateParam)
      this.copy(f = newSpec, body = newBody)
    }

    // Removed unused formals from this procedure
    // and corresponding actuals in all recursive calls;
    // a parameter is considered unused if it is only mentioned in a recursive call
    // at the same (or other unused) position
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
