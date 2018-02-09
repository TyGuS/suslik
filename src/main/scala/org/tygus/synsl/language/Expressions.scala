package org.tygus.synsl.language

import org.tygus.synsl.{PrettyPrinting, Substitutable}

/**
  * @author Ilya Sergey
  */

object Expressions {

  type Ident = String

  sealed abstract class Expr extends PrettyPrinting with Substitutable[Expr] {

    // Type-coercing visitor (yikes!)
    def collect[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(exp: Expr): Set[R] = exp match {
        case v@Var(name) if p(v) => acc + v.asInstanceOf[R]
        case c@PConst(value) if p(c) => acc + c.asInstanceOf[R]
        case b: BinaryExpr =>
          val acc1 = if (p(b)) acc + b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(b.left)
          collector(acc2)(b.right)
        case n@ENeg(arg) =>
          val acc1 = if (p(n)) acc + n.asInstanceOf[R] else acc
          collector(acc1)(arg)
        case _ => acc
      }

      collector(Set.empty)(this)
    }

    def vars: Set[Var] = collect(_.isInstanceOf[Var])

  }

  // Program-level variable: program-level or ghost
  case class Var(name: String) extends Expr {
    override def pp: String = name

    def subst(x: Var, by: Expr): Expr =
      if (x.name == this.name) by else this

  }

  // Program-level constant
  case class PConst(value: Any) extends Expr {
    override def pp: String = value.toString
    def subst(x: Var, by: Expr): Expr = this
  }

  sealed abstract class BinaryExpr(val left: Expr, val right: Expr) extends Expr {
  }

  // Binary expressions
  // TODO: Figure out how to use Scala's generic programming to solve this annoying instance of the expression problem
  case class EPlus(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right) {
    def subst(x: Var, by: Expr): Expr = EPlus(left.subst(x, by), right.subst(x, by))
  }

  case class EMinus(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right) {
    def subst(x: Var, by: Expr): Expr = EMinus(left.subst(x, by), right.subst(x, by))
  }

  case class ELeq(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right) {
    def subst(x: Var, by: Expr): Expr = ELeq(left.subst(x, by), right.subst(x, by))
  }

  case class ELtn(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right) {
    def subst(x: Var, by: Expr): Expr = ELtn(left.subst(x, by), right.subst(x, by))
  }

  case class EEq(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right) {
    def subst(x: Var, by: Expr): Expr = EEq(left.subst(x, by), right.subst(x, by))
  }

  case class EAnd(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right) {
    def subst(x: Var, by: Expr): Expr = EAnd(left.subst(x, by), right.subst(x, by))
  }

  case class EOr(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right) {
    def subst(x: Var, by: Expr): Expr = EOr(left.subst(x, by), right.subst(x, by))
  }

  case class ENeg(arg: Expr) extends Expr {
    def subst(x: Var, by: Expr): Expr = ENeg(arg.subst(x, by))
  }


}





