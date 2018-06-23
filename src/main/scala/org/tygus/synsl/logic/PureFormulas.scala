package org.tygus.synsl.logic

import org.tygus.synsl.language._
import org.tygus.synsl.language.Expressions._

/**
  * Pure fragment of the logic
  */
sealed abstract class PFormula extends PrettyPrinting with Substitutable[PFormula] with PureLogicUtils {

  // Collect certain sub-expressions
  def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
    // TODO: refactor into full CPS
    def collector(acc: Set[R])(phi: PFormula): Set[R] = phi match {
      case PTrue => acc
      case PFalse => acc
      case PLeq(left, right) => acc ++ left.collect(p) ++ right.collect(p)
      case PLtn(left, right) => acc ++ left.collect(p) ++ right.collect(p)
      case PEq(left, right) => acc ++ left.collect(p) ++ right.collect(p)
      case SEq(left, right) => acc ++ left.collect(p) ++ right.collect(p)
      case PAnd(left, right) => collector(collector(acc)(left))(right)
      case POr(left, right) => collector(collector(acc)(left))(right)
      case PNeg(arg) => collector(acc)(arg)
    }

    collector(Set.empty)(this)
  }

  override def pp: Ident = this.toExpr.pp

  def subst(sigma: Map[Var, Expr]): PFormula = fromExpr(this.toExpr.subst(sigma)).head

  def isTrue: Boolean = simplify(this) == PTrue

  def toExpr: Expr

  def vars: Set[Var] = this.collectE(_.isInstanceOf[Var])

  def implies(other: PFormula): PFormula = POr(PNeg(this), other)

}

object PTrue extends PFormula {
  override def toExpr: Expr = BoolConst(true)
}

object PFalse extends PFormula {
  override def toExpr: Expr = BoolConst(false)
}

// Connectives
case class PAnd(left: PFormula, right: PFormula) extends PFormula {
  override def toExpr: Expr = BinaryExpr(OpAnd, left.toExpr, right.toExpr)
}

case class POr(left: PFormula, right: PFormula) extends PFormula {
  override def toExpr: Expr = BinaryExpr(OpOr, left.toExpr, right.toExpr)
}

case class PNeg(arg: PFormula) extends PFormula {
  override def toExpr: Expr = UnaryExpr(OpNot, arg.toExpr)
}

/*
  Arithmetic expressions
 */
// Ф <= Ф', Ф < Ф'
case class PLeq(left: Expr, right: Expr) extends PFormula {
  override def toExpr: Expr = BinaryExpr(OpLeq, left, right)
}

case class PLtn(left: Expr, right: Expr) extends PFormula {
  override def toExpr: Expr = BinaryExpr(OpLt, left, right)
}

/*
  Primitive Equality
  Ф == Ф'
 */
case class PEq(left: Expr, right: Expr) extends PFormula {
  override def toExpr: Expr = BinaryExpr(OpEq, left, right)
}

/*
  Equality on finite sets
 */
case class SEq(left: Expr, right: Expr) extends PFormula {
  override def toExpr: Expr = BinaryExpr(OpEq, left, right)
}