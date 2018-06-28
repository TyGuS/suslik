package org.tygus.synsl.logic

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Expressions._

/**
  * Utilities for pure formulae
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */
trait PureLogicUtils {

  /*
  Substitutions
   */
  type Subst = Map[Var, Expr]
  type SubstVar = Map[Var, Var]

  protected def assertNoOverlap(sbst1: Subst, sbst2: Subst) {
    assert(sbst1.keySet.intersect(sbst2.keySet).isEmpty, s"Two substitutions overlap:\n:$sbst1\n$sbst2")
  }

  def compose(subst1: SubstVar, subst2: Subst): Subst = {
    subst1.map { case (k, v) => k -> subst2.getOrElse(v, v) }
  }

  def compose1(subst1: Subst, subst2: Subst): Subst =
    subst1.map {
      case (k, v) => k -> (v match {
        case w@Var(_) => subst2.getOrElse(w, v)
        case _ => v
      })
    }


  def ppSubst(m: Subst): String = {
    s"{${m.map { case (k, v) => s"${k.pp} -> ${v.pp}" }.mkString("; ")}}"
  }

  def agreeOnSameKeys(m1: Subst, m2: Subst): Boolean = {
    val common = m1.keySet.intersect(m2.keySet)
    common.forall(k => m1.isDefinedAt(k) && m2.isDefinedAt(k) && m1(k) == m2(k))
  }

  /**
    * Expression simplifier
    */
  def simplify(e: Expr): Expr = e match {
    //  Truth table for and
    case BinaryExpr(OpAnd, BoolConst(false), _) => pFalse
    case BinaryExpr(OpAnd, _, BoolConst(false)) => pFalse
    case BinaryExpr(OpAnd, BoolConst(true), right) => right
    case BinaryExpr(OpAnd, left, BoolConst(true)) => left

    //  Truth table for or
    case BinaryExpr(OpOr, BoolConst(true), _) => pTrue
    case BinaryExpr(OpOr, _, BoolConst(true)) => pTrue
    case BinaryExpr(OpOr, BoolConst(false), right) => right
    case BinaryExpr(OpOr, left, BoolConst(false)) => left

    //  Classical logic stuff and de Morgan
    case UnaryExpr(OpNot, UnaryExpr(OpNot, arg)) => simplify(arg)
    case UnaryExpr(OpNot, BinaryExpr(OpAnd, left, right)) => simplify(left.not) || simplify(right.not)
    case UnaryExpr(OpNot, BinaryExpr(OpOr, left, right)) => simplify(left.not) && simplify(right.not)
    case UnaryExpr(OpNot, BoolConst(true)) => pFalse
    case UnaryExpr(OpNot, BoolConst(false)) => pTrue

    case BinaryExpr(OpEq, v1@Var(n1), v2@Var(n2)) => // sort arguments lexicographically
      if (n1.toString <= n2.toString) BinaryExpr(OpEq, v1, v2) else BinaryExpr(OpEq, v2, v1)
    case BinaryExpr(OpEq, e, v@Var(_)) if !e.isInstanceOf[Var] => BinaryExpr(OpEq, v, simplify(e))

    case BinaryExpr(OpPlus, left, IntConst(i)) if i.toInt == 0 => simplify(left)
    case BinaryExpr(OpPlus, IntConst(i), right) if i.toInt == 0 => simplify(right)
    case BinaryExpr(OpMinus, left, IntConst(i)) if i.toInt == 0 => simplify(left)

    case BinaryExpr(OpUnion, left, SetLiteral(s)) if s.isEmpty => simplify(left)
    case BinaryExpr(OpUnion, SetLiteral(s), right) if s.isEmpty => simplify(right)

    case UnaryExpr(op, e1) => UnaryExpr(op, simplify(e1))
    case BinaryExpr(op, e1, e2) => BinaryExpr(op, simplify(e1), simplify(e2))

    case _ => e
  }

  def pTrue: PFormula = BoolConst(true)

  def pFalse: PFormula = BoolConst(false)

  def andClean(p1: PFormula, p2: PFormula): PFormula = simplify(p1 && p2)

  private def isAtomicExpr(e: Expr): Boolean = e match {
    case BinaryExpr(op, _, _) => !op.isInstanceOf[RelOp] && !op.isInstanceOf[LogicOp]
    case _ => true
  }

  val isRelationPFormula: (PFormula) => Boolean = {
    case BinaryExpr(op, e1, e2) => op.isInstanceOf[RelOp] && isAtomicExpr(e1) && isAtomicExpr(e2)
    case _ => false
  }

  val isAtomicPFormula: (PFormula) => Boolean = {
    case BoolConst(true) | BoolConst(false) => true
    case UnaryExpr(OpNot, p) => isRelationPFormula(p)
    case p => isRelationPFormula(p)
  }

  def isCNF(isAtom: PFormula => Boolean)(pf: PFormula): Boolean = {
    def check(phi: PFormula): Boolean = phi match {
      case BinaryExpr(OpOr, _, _) => false
      case BinaryExpr(OpAnd, left, right) => check(left) && check(right)
      case p => isAtom(p)
    }

    check(simplify(pf))
  }

  /**
    * Return the formula as a list of conjuncts
    */
  def conjuncts(phi: PFormula): List[PFormula] = {

    val pf = simplify(phi)
    if (!isCNF(isAtomicPFormula)(pf)) {
      throw PureLogicException(s"The formula ${phi.pp} is not in CNF")
    }

    def _conjuncts(p: PFormula): List[PFormula] = p match {
      case BoolConst(true) => Nil
      case atom if isAtomicPFormula(atom) => List(atom)
      case BinaryExpr(OpAnd, left, right) => _conjuncts(left) ++ _conjuncts(right)
      case x => throw PureLogicException(s"Not a conjunction or an atomic pure formula: ${x.pp}")
    }

    _conjuncts(pf).distinct
  }

  def findCommon[T](cond: T => Boolean, ps1: List[T], ps2: List[T]): Option[(T, List[T], List[T])] = {
    for (p <- ps1 if cond(p)) {
      if (ps2.contains(p)) {
        return Some((p, ps1.filter(_ != p), ps2.filter(_ != p)))
      }
    }
    None
  }

  def findConjunctAndRest(p: PFormula => Boolean, phi: PFormula): Option[(PFormula, List[PFormula])] =
    Some(conjuncts(phi)).flatMap(cs => cs.find(p) match {
      case Some(c) => Some((c, cs.filter(e => e != c)))
      case None => None
    })

  /**
    * Assemble a formula from a list of conjunctions
    */
  def mkConjunction(ps: List[PFormula]): PFormula = ps.distinct.foldLeft[PFormula](pTrue)(andClean)

  /**
    * @param vs    a list of variables to refresh
    * @param bound bound identifiers
    * @return A substitution from old vars in assn to new ones, fresh wrt. `rotten`
    */
  def refreshVars(vs: List[Var], bound: Set[Var]): Map[Var, Var] = {

    def go(vsToRefresh: List[Var], taken: Set[Var], acc: Map[Var, Var]): Map[Var, Var] =
      vsToRefresh match {
        case Nil => acc
        case x :: xs =>
          val y = x.refresh(taken)
          val newAcc = acc + (x -> y)
          val newTaken = taken + x + y
          go(xs, newTaken, newAcc)
      }

    go(vs, bound, Map.empty)
  }

}

case class PureLogicException(msg: String) extends SynSLException("pure", msg)