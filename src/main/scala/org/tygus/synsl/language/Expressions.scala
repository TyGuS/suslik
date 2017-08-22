package org.tygus.synsl.language

import org.tygus.synsl.PrettyPrinting

/**
  * @author Ilya Sergey
  */

object Expressions {

  sealed abstract class Expr extends PrettyPrinting {
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

  }

  // Program-level variable: program-level or ghost
  case class Var(name: String) extends Expr {
    override def pp: String = name
  }

  // Program-level constant
  case class PConst(value: Any) extends Expr {
    override def pp: String = value.toString
  }

  abstract class BinaryExpr(val left: Expr, val right: Expr) extends Expr

  // Binary expressions
  case class EPlus(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right)
  case class EMinus(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right)
  case class ELeq(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right)
  case class ELtn(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right)
  case class EEq(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right)
  case class EAnd(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right)
  case class EOr(override val left: Expr, override val right: Expr) extends BinaryExpr(left, right)
  case class ENeg(arg: Expr) extends Expr


}





