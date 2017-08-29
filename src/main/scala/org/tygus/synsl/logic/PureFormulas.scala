package org.tygus.synsl.logic

import org.tygus.synsl.language.Expressions.{Expr, Var}
import org.tygus.synsl.{PrettyPrinting, Substitutable}

/**
  * Pure fragment of the logic
  */
trait PureFormulas {

  type Ident = String

  sealed abstract class PureFormula extends PrettyPrinting with Substitutable[PureFormula] {

    // Collect certain sub-expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
      // TODO: refactor into full CPS
      def collector(acc: Set[R])(phi: PureFormula): Set[R] = phi match {
        case PTrue => acc
        case PFalse => acc
        case PLeq(left, right) => left.collect(p) ++ right.collect(p)
        case PLtn(left, right) => left.collect(p) ++ right.collect(p)
        case PEq(left, right) => left.collect(p) ++ right.collect(p)
        case PAnd(left, right) => collector(collector(acc)(left))(right)
        case POr(left, right) => collector(collector(acc)(left))(right)
        case PNeg(arg) => collector(acc)(arg)
        case _ => acc

      }
      collector(Set.empty)(this)
    }

  }

  object PTrue extends PureFormula {
    override def pp: Ident = "true"
    def subst(x: Var, by: Expr): PureFormula = this
  }

  object PFalse extends PureFormula {
    override def pp: Ident = "false"
    def subst(x: Var, by: Expr): PureFormula = this
  }

  // Ф <= Ф', Ф < Ф', Ф == Ф'
  case class PLeq(left: Expr, right: Expr) extends PureFormula {
    override def pp: Ident = s"${left.pp} <= ${right.pp}"
    def subst(x: Var, by: Expr): PureFormula = PLeq(left.subst(x, by), right.subst(x, by))
  }

  case class PLtn(left: Expr, right: Expr) extends PureFormula {
    override def pp: Ident = s"${left.pp} < ${right.pp}"
    def subst(x: Var, by: Expr): PureFormula = PLtn(left.subst(x, by), right.subst(x, by))
  }

  case class PEq(left: Expr, right: Expr) extends PureFormula {
    override def pp: Ident = s"${left.pp} = ${right.pp}"
    def subst(x: Var, by: Expr): PureFormula = PEq(left.subst(x, by), right.subst(x, by))
  }

  // Connectives
  case class PAnd(left: PureFormula, right: PureFormula) extends PureFormula {
    override def pp: Ident = s"(${left.pp} /\\ ${right.pp})"
    def subst(x: Var, by: Expr): PureFormula = PAnd(left.subst(x, by), right.subst(x, by))
  }

  case class POr(left: PureFormula, right: PureFormula) extends PureFormula {
    override def pp: Ident = s"(${left.pp} \\/ ${right.pp})"
    def subst(x: Var, by: Expr): PureFormula = POr(left.subst(x, by), right.subst(x, by))
  }

  case class PNeg(arg: PureFormula) extends PureFormula {
    override def pp: Ident = s"~~${arg.pp}"
    def subst(x: Var, by: Expr): PureFormula = PNeg(arg.subst(x, by))
  }

}
