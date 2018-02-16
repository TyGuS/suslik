package org.tygus.synsl.language

/**
  * @author Ilya Sergey
  */

object Expressions {

  sealed abstract class UnOp extends PrettyPrinting {}
  object OpNot extends UnOp {
    override def pp: String = "not"
  }

  sealed abstract class BinOp extends PrettyPrinting {}
  object OpPlus extends BinOp {
    override def pp: String = "+"
  }
  object OpMinus extends BinOp {
    override def pp: String = "-"
  }
  object OpEq extends BinOp {
    override def pp: String = "=="
  }
  object OpLeq extends BinOp {
    override def pp: String = "<="
  }
  object OpLt extends BinOp {
    override def pp: String = "<"
  }
  object OpAnd extends BinOp {
    override def pp: String = "&&"
  }
  object OpOr extends BinOp {
    override def pp: String = "||"
  }

  sealed abstract class Expr extends PrettyPrinting with Substitutable[Expr] {

    // Type-coercing visitor (yikes!)
    def collect[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(exp: Expr): Set[R] = exp match {
        case v@Var(_) if p(v) => acc + v.asInstanceOf[R]
        case c@PConst(_) if p(c) => acc + c.asInstanceOf[R]
        case b@BinaryExpr(_, l, r) =>
          val acc1 = if (p(b)) acc + b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          collector(acc2)(r)
        case u@UnaryExpr(_, arg) =>
          val acc1 = if (p(u)) acc + u.asInstanceOf[R] else acc
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

    def subst(sigma: Map[Var, Expr]): Expr =
      sigma.getOrElse(this, this)
  }

  // Program-level constant
  case class PConst(value: Any) extends Expr {
    override def pp: String = value.toString
    def subst(sigma: Map[Var, Expr]): Expr = this
  }

  case class BinaryExpr(op: BinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = BinaryExpr(op, left.subst(sigma), right.subst(sigma))

    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"
  }

  case class UnaryExpr(op: UnOp, arg: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = UnaryExpr(op, arg.subst(sigma))

    override def pp: String = s"${op.pp} ${arg.pp}"
  }

}




