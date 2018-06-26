package org.tygus.synsl.language

/**
  * @author Ilya Sergey
  */

object Expressions {

  sealed abstract class UnOp extends PrettyPrinting {}
  object OpNot extends UnOp {
    override def pp: String = "not"
  }

  sealed abstract class BinOp extends PrettyPrinting {
    def level: Int
    def associative: Boolean = false
  }

  object OpPlus extends BinOp {
    def level: Int = 4
    override def associative: Boolean = true
    override def pp: String = "+"
  }
  object OpMinus extends BinOp {
    def level: Int = 4
    override def pp: String = "-"
  }
  object OpEq extends BinOp {
    def level: Int = 3
    override def pp: String = "=="
  }
  object OpLeq extends BinOp {
    def level: Int = 3
    override def pp: String = "<="
  }
  object OpLt extends BinOp {
    def level: Int = 3
    override def pp: String = "<"
  }
  object OpAnd extends BinOp {
    def level: Int = 2
    override def associative: Boolean = true
    override def pp: String = "/\\"
  }
  object OpOr extends BinOp {
    def level: Int = 2
    override def associative: Boolean = true
    override def pp: String = "\\/"
  }
  object OpUnion extends BinOp {
    def level: Int = 4
    override def associative: Boolean = true
    override def pp: String = "++"
  }
  object OpIn extends BinOp {
    def level: Int = 3
    override def pp: String = "in"
  }
  object OpSetEq extends BinOp {
    def level: Int = 3
    override def pp: String = "=i"
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
        case s@SetLiteral(elems) =>
          val acc1 = if (p(s)) acc + s.asInstanceOf[R] else acc
          elems.foldLeft(acc1)((a,e) => collector(a)(e))
        case c@IntConst(i) => if (p(c)) acc + c.asInstanceOf[R] else acc
        case i@IfThenElse(cond, l, r) =>
          val acc1 = if (p(i)) acc + i.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(cond)
          val acc3 = collector(acc2)(l)
          collector(acc3)(r)
      }

      collector(Set.empty)(this)
    }

    def vars: Set[Var] = collect(_.isInstanceOf[Var])

    override def pp: String

    def level: Int = 6
    def associative: Boolean = false

    def printAtLevel(lvl: Int): String = {
      val s = pp
      if (lvl < this.level) s
      else if (lvl == this.level && associative) s
      else s"($s)"
    }
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
        count = count + 1
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
    override def level: Int = op.level
    override def associative: Boolean = op.associative
    override def pp: String = s"${left.printAtLevel(level)} ${op.pp} ${right.printAtLevel(level)}"

  }

  case class UnaryExpr(op: UnOp, arg: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = UnaryExpr(op, arg.subst(sigma))

    override def level = 5
    override def pp: String = s"${op.pp} ${arg.printAtLevel(level)}"
  }

  case class SetLiteral(elems: List[Expr]) extends Expr {
    override def pp: String = s"{${elems.map(_.pp).mkString(", ")}}"
    override def subst(sigma: Map[Var, Expr]): SetLiteral = SetLiteral(elems.map(_.subst(sigma)))
  }

  case class IfThenElse(cond: Expr, left: Expr, right: Expr) extends Expr {
    override def level: Int = 1
    override def pp: String = s"${cond.printAtLevel(level)} ? ${left.printAtLevel(level)} : ${right.printAtLevel(level)}"
    override def subst(sigma: Map[Var, Expr]): IfThenElse = IfThenElse(cond.subst(sigma), left.subst(sigma), right.subst(sigma))

  }

}




