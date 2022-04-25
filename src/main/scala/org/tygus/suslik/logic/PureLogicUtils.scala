package org.tygus.suslik.logic

import org.tygus.suslik.SSLException
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.synthesis.SynthesisException

/**
  * Utilities for pure formulae
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */
trait PureLogicUtils {

  def emptySubst: Subst = Map.empty

  protected def assertNoOverlap(sbst1: Subst, sbst2: Subst) {
    assert(sbst1.keySet.intersect(sbst2.keySet).isEmpty, s"Two substitutions overlap:\n:$sbst1\n$sbst2")
  }

  def compose(subst1: Subst, subst2: Subst): Subst = subst1.map { case (k, e) => k -> e.subst(subst2) }

  def ppSubst(m: Subst): String = {
    s"{${m.map { case (k, v) => s"${k.pp} -> ${v.pp}" }.mkString("; ")}}"
  }

  /**
    *
    */
  def propagate_not(e:Expr):Expr = e match {
    //  Classical logic stuff and de Morgan
    case UnaryExpr(OpNot, UnaryExpr(OpNot, arg)) => propagate_not(arg)
    case UnaryExpr(OpNot, BinaryExpr(OpAnd, left, right)) => propagate_not(left.not) || propagate_not(right.not)
    case UnaryExpr(OpNot, BinaryExpr(OpOr, left, right)) => propagate_not(left.not) && propagate_not(right.not)
    case UnaryExpr(OpNot, BoolConst(true)) => eFalse
    case UnaryExpr(OpNot, BoolConst(false)) => eTrue
      
    // Propagate further
    case UnaryExpr(op, e1) => UnaryExpr(op, propagate_not(e1))
    case BinaryExpr(op, left, right) => BinaryExpr(op, propagate_not(left), propagate_not(right))
    case OverloadedBinaryExpr(op, e1, e2) => OverloadedBinaryExpr(op, propagate_not(e1), propagate_not(e2))
    case _:IntConst => e
    case _:LocConst => e
    case _:BoolConst => e
    case _:Var => e
    case IfThenElse(e1,e2,e3) => IfThenElse(propagate_not(e1),propagate_not(e2), propagate_not(e3))
    case SetLiteral(args) => SetLiteral(args.map(propagate_not))
    case e => throw SynthesisException(s"Not supported: ${e.pp} (${e.getClass.getName})")
  }

  def desugar(e: Expr): Expr = e match {
      // Bi-implication usually ends up not being in CNF, so it is not very useful
//    case BinaryExpr(OpBoolEq, e1, e2) => desugar(e1) <==> desugar(e2)
    case UnaryExpr(OpUnaryMinus, arg) => BinaryExpr(OpMinus, IntConst(0), desugar(arg))
    case OverloadedBinaryExpr(OpNotEqual, e1, e2)  => desugar(e1) |/===| desugar(e2)
    case OverloadedBinaryExpr(OpGt, e1, e2)  => OverloadedBinaryExpr(OpLt, desugar(e2), desugar(e1))
    case OverloadedBinaryExpr(OpGeq, e1, e2)  => OverloadedBinaryExpr(OpLeq, desugar(e2), desugar(e1))
    case BinaryExpr(OpImplication, e1, e2)           => desugar(e1) ==> desugar(e2)
    case OverloadedBinaryExpr(OpImplication, e1, e2) => desugar(e1) ==> desugar(e2)

      // Propagate further
    case BinaryExpr(op, e1, e2) => BinaryExpr(op, desugar(e1), desugar(e2))
    case OverloadedBinaryExpr(op, e1, e2) => OverloadedBinaryExpr(op, desugar(e1), desugar(e2))
    case UnaryExpr(op, e1) => UnaryExpr(op, desugar(e1))
    case _:IntConst => e
    case _:LocConst => e
    case _:BoolConst => e
    case _:Var => e
    case IfThenElse(e1,e2,e3) => IfThenElse(desugar(e1),desugar(e2), desugar(e3))
    case SetLiteral(args) => SetLiteral(args.map(desugar))
    case e => throw SynthesisException(s"Not supported: ${e.pp} (${e.getClass.getName})")
  }

  /**
    * Expression simplifier
    */
  def simplify(e: Expr): Expr = e match {
    //  Truth table for and
    case BinaryExpr(OpAnd, e1, e2) => simplify(e1) match {
      case BoolConst(false) => eFalse
      case BoolConst(true) => simplify(e2)
      case s1 => simplify(e2) match {
        case BoolConst(false) => eFalse
        case BoolConst(true) => s1
        case s2 => s1 && s2
      }
    }

    //  Truth table for or
    case BinaryExpr(OpOr, e1, e2) => simplify(e1) match {
      case BoolConst(true) => eTrue
      case BoolConst(false) => simplify(e2)
      case s1 => simplify(e2) match {
        case BoolConst(true) => eTrue
        case BoolConst(false) => s1
        case s2 => s1 || s2
      }
    }

    //  Classical logic stuff and de Morgan
    case UnaryExpr(OpNot, UnaryExpr(OpNot, arg)) => simplify(arg)
    case UnaryExpr(OpNot, BinaryExpr(OpAnd, left, right)) => simplify(left.not) || simplify(right.not)
    case UnaryExpr(OpNot, BinaryExpr(OpOr, left, right)) => simplify(left.not) && simplify(right.not)
    case UnaryExpr(OpNot, BoolConst(true)) => eFalse
    case UnaryExpr(OpNot, BoolConst(false)) => eTrue

    case BinaryExpr(OpEq, Var(n1), Var(n2)) if n1 == n2 => // remove trivial equality
      BoolConst(true)
    case BinaryExpr(OpEq, v1@Var(n1), v2@Var(n2)) => // sort arguments lexicographically
      if (n1 <= n2) BinaryExpr(OpEq, v1, v2) else BinaryExpr(OpEq, v2, v1)
    case BinaryExpr(OpEq, e, v@Var(_)) if !e.isInstanceOf[Var] => BinaryExpr(OpEq, v, simplify(e))
    case BinaryExpr(OpSetEq, Var(n1), Var(n2)) if n1 == n2 => // remove trivial equality
      BoolConst(true)
    case BinaryExpr(OpSetEq, v1@Var(n1), v2@Var(n2)) => // sort arguments lexicographically
      if (n1 <= n2) BinaryExpr(OpSetEq, v1, v2) else BinaryExpr(OpSetEq, v2, v1)
    case BinaryExpr(OpSetEq, e, v@Var(_)) if !e.isInstanceOf[Var] => BinaryExpr(OpSetEq, v, simplify(e))

      // TODO: maybe enable
//    case BinaryExpr(OpBoolEq, v1@Var(n1), v2@Var(n2)) if n1 == n2 => // remove trivial equality
//      BoolConst(true)
//    case BinaryExpr(OpBoolEq, v1@Var(n1), v2@Var(n2)) => // sort arguments lexicographically
//      if (n1 <= n2) BinaryExpr(OpBoolEq, v1, v2) else BinaryExpr(OpBoolEq, v2, v1)
//    case BinaryExpr(OpBoolEq, e, v@Var(_)) if !e.isInstanceOf[Var] => BinaryExpr(OpBoolEq, v, simplify(e))

    case BinaryExpr(OpPlus, left, IntConst(i)) if i.toInt == 0 => simplify(left)
    case BinaryExpr(OpPlus, IntConst(i), right) if i.toInt == 0 => simplify(right)
    case BinaryExpr(OpMinus, left, IntConst(i)) if i.toInt == 0 => simplify(left)

    case BinaryExpr(OpUnion, left, SetLiteral(s)) if s.isEmpty => simplify(left)
    case BinaryExpr(OpUnion, SetLiteral(s), right) if s.isEmpty => simplify(right)

    case UnaryExpr(op, e1) => UnaryExpr(op, simplify(e1))
    case BinaryExpr(op, e1, e2) => BinaryExpr(op, simplify(e1), simplify(e2))

    case _ => e
  }

  def pTrue: PFormula = PFormula(Set[Expr]())

  def pFalse: PFormula = PFormula(Set(eFalse))

  def simplify(p: PFormula): PFormula = {
    val cs = p.conjuncts.map(simplify) - eTrue
    if (cs.contains(eFalse)) pFalse else PFormula(cs)
  }

  def findCommon[T](cond: T => Boolean, ps1: List[T], ps2: List[T]): Option[(T, List[T], List[T])] = {
    for (p <- ps1 if cond(p)) {
      if (ps2.contains(p)) {
        return Some((p, ps1.filter(_ != p), ps2.filter(_ != p)))
      }
    }
    None
  }

  def findConjunctAndRest[T](p: Expr => Option[T], phi: PFormula): Option[(T, PFormula)] = {
    for (c <- phi.conjuncts) {
      p(c) match {
        case Some(res) => return Some(res, phi - c)
        case None => None
      }
    }
    None
  }

  def extractEquality(e: Expr): Option[(Expr, Expr)] = e match {
    case BinaryExpr(OpEq, l, r) => Some(l, r)
    case BinaryExpr(OpBoolEq, l, r) => Some(l, r)
    case BinaryExpr(OpSetEq, l, r) => Some(l, r)
    case BinaryExpr(OpIntervalEq, l, r) => Some(l, r)
    case _ => None
  }

  /**
    * Assemble a formula from a list of conjunctions
    */
  def toFormula(e: Expr): PFormula = PFormula(e.conjuncts.toSet)

  // Variable name with a given prefix that does not appear in taken
  def freshVar(taken: Set[Var], prefix: String): Var = {
    val safePrefix = prefix.filter(c => c.isLetterOrDigit || c == '_').dropWhile(_.isDigit)
    var count = 1
    var tmpName = safePrefix
    while (taken.exists(_.name == tmpName)) {
      tmpName = safePrefix + count
      count = count + 1
    }
    Var(tmpName)
  }

  /**
    * @param vs    a list of variables to refresh
    * @param bound identifiers whose names are already taken
    * @return A substitution from old vars in assn to new ones, fresh wrt. `rotten`
    */
  def refreshVars(vs: List[Var], bound: Set[Var], suffix: String = ""): SubstVar = {

    def go(vsToRefresh: List[Var], taken: Set[Var], acc: Map[Var, Var]): SubstVar =
      vsToRefresh match {
        case Nil => acc
        case x :: xs =>
          val y = freshVar(taken, x.name + suffix)
          val newAcc = acc + (x -> y)
          val newTaken = taken + x + y
          go(xs, newTaken, newAcc)
      }

    go(vs, bound, Map.empty)
  }

  def nubBy[A,B](l:List[A], p:A=>B):List[A] =
  {
    def go[A,B](l:List[A], p:A=>B, s:Set[B], acc:List[A]):List[A] = l match
    {
      case Nil => acc.reverse
      case x::xs if s.contains(p(x)) => go(xs,p,s,acc)
      case x::xs                     => go(xs,p,s+p(x),x::acc)
    }
    go(l,p,Set.empty,Nil)
  }


}

case class PureLogicException(msg: String) extends SSLException("pure", msg)