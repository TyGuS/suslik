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
        case c@IntConst(_) if p(c) => acc + c.asInstanceOf[R]
        case c@BoolConst(_) if p(c) => acc + c.asInstanceOf[R]
        case b@BinaryExpr(_, l, r) =>
          val acc1 = if (p(b)) acc + b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          collector(acc2)(r)
        case u@UnaryExpr(_, arg) =>
          val acc1 = if (p(u)) acc + u.asInstanceOf[R] else acc
          collector(acc1)(arg)
        case EmptySet => acc
        case u@SetUnion(l, r) =>
          val acc1 = if (p(u)) acc + u.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          collector(acc2)(r)
        case s@SingletonSet(e) =>
          val acc1 = if (p(s)) acc + s.asInstanceOf[R] else acc
          collector(acc1)(e)
        case c@IntConst(i) => if (p(c)) acc + c.asInstanceOf[R] else acc
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

    def refresh(taken: Set[Var]): Var = {
      var count = 1
      val original = this.name
      var tmpName = original
      while (taken.exists(_.name == tmpName)) {
        tmpName = original + count
      }
      Var(tmpName)
    }
  }

  // Program-level constant
  abstract class Const(value: Any) extends Expr {
    override def pp: String = value.toString
    def subst(sigma: Map[Var, Expr]): Expr = this
  }

  case class IntConst(value: Integer) extends Const(value) {
    /**
      * Let's have this instead of the dedicated Nil constructor
      */
    def isNull: Boolean = value == 0
  }

  val NilPtr = IntConst(0)

  case class BoolConst(value: Boolean) extends Const(value)

  case class BinaryExpr(op: BinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = BinaryExpr(op, left.subst(sigma), right.subst(sigma))

    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"
  }

  case class UnaryExpr(op: UnOp, arg: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = UnaryExpr(op, arg.subst(sigma))

    override def pp: String = s"${op.pp} ${arg.pp}"
  }

  /** **********************************************************************
    * Finite sets and operations on them
    * **********************************************************************/

  abstract sealed class SetExpr extends Expr {
    override def subst(sigma: Map[Var, Expr]): SetExpr
  }

  object EmptySet extends SetExpr {
    override def pp: String = "Empty"
    def subst(sigma: Map[Var, Expr]): this.type = EmptySet
  }

  case class SetUnion(l: Expr, r: Expr) extends SetExpr {
    def subst(sigma: Map[Var, Expr]): SetUnion = SetUnion(l.subst(sigma), r.subst(sigma))
    override def pp: String = s"Union(${l.pp}, ${r.pp})"
  }

  case class SingletonSet(e: Expr) extends SetExpr {
    override def pp: String = s"{${e.pp}}"
    override def subst(sigma: Map[Var, Expr]): SingletonSet = SingletonSet(e.subst(sigma))
  }

}




