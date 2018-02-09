package org.tygus.synsl.logic

import org.tygus.synsl.language.Expressions.{Expr, Var, Ident}
import org.tygus.synsl.{PrettyPrinting, Substitutable}

/**
  * Pure fragment of the logic
  */
trait PureFormulas {

  sealed abstract class PFormula extends PrettyPrinting with Substitutable[PFormula] {

    // Collect certain sub-expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
      // TODO: refactor into full CPS
      def collector(acc: Set[R])(phi: PFormula): Set[R] = phi match {
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

  object PTrue extends PFormula {
    override def pp: Ident = "true"
    def subst(x: Var, by: Expr): PFormula = this
  }

  object PFalse extends PFormula {
    override def pp: Ident = "false"
    def subst(x: Var, by: Expr): PFormula = this
  }

  // Ф <= Ф', Ф < Ф', Ф == Ф'
  case class PLeq(left: Expr, right: Expr) extends PFormula {
    override def pp: Ident = s"${left.pp} <= ${right.pp}"
    def subst(x: Var, by: Expr): PFormula = PLeq(left.subst(x, by), right.subst(x, by))
  }

  case class PLtn(left: Expr, right: Expr) extends PFormula {
    override def pp: Ident = s"${left.pp} < ${right.pp}"
    def subst(x: Var, by: Expr): PFormula = PLtn(left.subst(x, by), right.subst(x, by))
  }

  case class PEq(left: Expr, right: Expr) extends PFormula {
    override def pp: Ident = s"${left.pp} == ${right.pp}"
    def subst(x: Var, by: Expr): PFormula = PEq(left.subst(x, by), right.subst(x, by))
  }

  // Connectives
  case class PAnd(left: PFormula, right: PFormula) extends PFormula {
    override def pp: Ident = s"(${left.pp} /\\ ${right.pp})"
    def subst(x: Var, by: Expr): PFormula = PAnd(left.subst(x, by), right.subst(x, by))
  }

  case class POr(left: PFormula, right: PFormula) extends PFormula {
    override def pp: Ident = s"(${left.pp} \\/ ${right.pp})"
    def subst(x: Var, by: Expr): PFormula = POr(left.subst(x, by), right.subst(x, by))
  }

  case class PNeg(arg: PFormula) extends PFormula {
    override def pp: Ident = s"not (${arg.pp})"
    def subst(x: Var, by: Expr): PFormula = PNeg(arg.subst(x, by))
  }

}
