package org.tygus.synsl.language

import org.tygus.synsl.logic.Gamma

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
    def lType: SynslType
    def rType: SynslType
    def resType: SynslType
  }

  sealed abstract class RelOp extends BinOp {
    def resType: SynslType = BoolType
  }
  sealed abstract class LogicOp extends BinOp {
    def lType: SynslType = BoolType
    def rType: SynslType = BoolType
    def resType: SynslType = BoolType
  }
  trait SymmetricOp
  trait AssociativeOp

  object OpPlus extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "+"
    def lType: SynslType = IntType
    def rType: SynslType = IntType
    def resType: SynslType = IntType
  }
  object OpMinus extends BinOp {
    def level: Int = 4
    override def pp: String = "-"
    def lType: SynslType = IntType
    def rType: SynslType = IntType
    def resType: SynslType = IntType
  }
  object OpEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=="
    def lType: SynslType = IntType
    def rType: SynslType = IntType
  }
  object OpLeq extends RelOp {
    def level: Int = 3
    override def pp: String = "<="
    def lType: SynslType = IntType
    def rType: SynslType = IntType
  }
  object OpLt extends RelOp {
    def level: Int = 3
    override def pp: String = "<"
    def lType: SynslType = IntType
    def rType: SynslType = IntType
  }
  object OpAnd extends LogicOp with SymmetricOp with AssociativeOp {
    def level: Int = 2
    override def pp: String = "/\\"
  }
  object OpOr extends LogicOp with SymmetricOp with AssociativeOp {
    def level: Int = 2
    override def pp: String = "\\/"
  }
  object OpUnion extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "++"
    def lType: SynslType = IntSetType
    def rType: SynslType = IntSetType
    def resType: SynslType = IntSetType
  }
  object OpIn extends RelOp {
    def level: Int = 3
    override def pp: String = "in"
    def lType: SynslType = IntType
    def rType: SynslType = IntSetType
  }
  object OpSetEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=i"
    def lType: SynslType = IntSetType
    def rType: SynslType = IntSetType
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
        case _ => acc
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

    // Convenience operators for building expressions
    def |=| (other: Expr): Expr = BinaryExpr(OpEq, this, other)
    def |/=| (other: Expr): Expr = (this |=| other).not
    def not: Expr = UnaryExpr(OpNot, this)
    def && (other: Expr): Expr = BinaryExpr(OpAnd, this, other)
    def || (other: Expr): Expr = BinaryExpr(OpOr, this, other)
    def ==> (other: Expr): Expr = this.not || other

    def getType(gamma: Gamma): Option[SynslType]

    def resolve(gamma: Gamma, target: Option[SynslType]): Option[Gamma] = this match {
      case v@Var(_) => gamma.get(v) match {
        case Some(t) => if (t.conformsTo(target)) Some(gamma) else None
        case None => target match {
          case Some(t1) => Some(gamma + (v -> t1))
          case None => Some(gamma)
        }
      }
      case BoolConst(_) => if (BoolType.conformsTo(target)) Some(gamma) else None
      case IntConst(_) => if (IntType.conformsTo(target)) Some(gamma) else None
      case UnaryExpr(op, e) => op match {
        case OpNot => if (BoolType.conformsTo(target)) e.resolve(gamma, Some(BoolType)) else None
      }
      case BinaryExpr(op, l, r) =>
        if (op.resType.conformsTo(target)) {
          for {
            gamma1 <- l.resolve(gamma, Some(op.lType))
            gamma2 <- r.resolve(gamma1, Some(op.rType))
          } yield gamma2
        } else None
      case SetLiteral(elems) =>
        if (IntSetType.conformsTo(target)) {
          elems.foldLeft[Option[Map[Var, SynslType]]](Some(gamma))((go, e) => go match {
            case None => None
            case Some(g) => e.resolve(g, Some(IntType))
          })
        } else None
      case IfThenElse(c, t, e) =>
        for {
          gamma1 <- c.resolve(gamma, Some(BoolType))
          gamma2 <- t.resolve(gamma1, None)
          t1 = t.getType(gamma2)
          gamma3 <- e.resolve(gamma2, t1)
          t2 = e.getType(gamma3)
          gamma4 <- t2 match {
            case Some(_) => t.resolve(gamma3, t2) // RHS has more information: resolve LHS again
            case None => {
              assert(false, s"ITE with unconstrained types on both sides: $pp")
              None
            }
          }
        } yield gamma4
    }
  }

  type PFormula = Expr

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

    def getType(gamma: Map[Var, SynslType]): Option[SynslType] = gamma.get(this)
  }

  // Program-level constant
  sealed abstract class Const(value: Any) extends Expr {
    override def pp: String = value.toString
    def subst(sigma: Map[Var, Expr]): Expr = this
  }

  case class IntConst(value: Integer) extends Const(value) {
    /**
      * Let's have this instead of the dedicated Nil constructor
      */
    def isNull: Boolean = value == 0

    def getType(gamma: Map[Var, SynslType]): Option[SynslType] = Some(IntType)
  }

  val NilPtr = IntConst(0)

  case class BoolConst(value: Boolean) extends Const(value) {
    def getType(gamma: Map[Var, SynslType]): Option[SynslType] = Some(BoolType)
  }

  case class BinaryExpr(op: BinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = BinaryExpr(op, left.subst(sigma), right.subst(sigma))
    override def level: Int = op.level
    override def associative: Boolean = op.isInstanceOf[AssociativeOp]
    override def pp: String = s"${left.printAtLevel(level)} ${op.pp} ${right.printAtLevel(level)}"
    def getType(gamma: Map[Var, SynslType]): Option[SynslType] = Some(op.resType)
  }

  case class UnaryExpr(op: UnOp, arg: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = UnaryExpr(op, arg.subst(sigma))

    override def level = 5
    override def pp: String = s"${op.pp} ${arg.printAtLevel(level)}"
    def getType(gamma: Map[Var, SynslType]): Option[SynslType] = Some(BoolType)
  }

  case class SetLiteral(elems: List[Expr]) extends Expr {
    override def pp: String = s"{${elems.map(_.pp).mkString(", ")}}"
    override def subst(sigma: Map[Var, Expr]): SetLiteral = SetLiteral(elems.map(_.subst(sigma)))
    def getType(gamma: Map[Var, SynslType]): Option[SynslType] = Some(IntSetType)
  }

  case class IfThenElse(cond: Expr, left: Expr, right: Expr) extends Expr {
    override def level: Int = 1
    override def pp: String = s"${cond.printAtLevel(level)} ? ${left.printAtLevel(level)} : ${right.printAtLevel(level)}"
    override def subst(sigma: Map[Var, Expr]): IfThenElse = IfThenElse(cond.subst(sigma), left.subst(sigma), right.subst(sigma))
    def getType(gamma: Map[Var, SynslType]): Option[SynslType] = left.getType(gamma)
  }

}




