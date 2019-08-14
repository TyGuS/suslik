package org.tygus.suslik.language

import org.tygus.suslik.logic.Gamma
import org.tygus.suslik.synthesis.SynthesisException

/**
  * @author Ilya Sergey
  */

object Expressions {

  sealed abstract class UnOp extends PrettyPrinting {}
  object OpNot extends UnOp {
    override def pp: String = "not"
  }


  sealed abstract class BinOp extends OverloadedBinOp {
    def lType:SSLType
    def rType: SSLType

    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map((lType, rType) -> this)

    override def default: BinOp = this

    def resType: SSLType
  }

  sealed abstract class OverloadedBinOp extends PrettyPrinting {
    def opFromTypes: Map[(SSLType, SSLType), BinOp]
    def default: BinOp
    def level:Int
  }

  sealed abstract class RelOp extends BinOp {
    def resType: SSLType = BoolType
  }
  sealed abstract class LogicOp extends BinOp {
    def lType: SSLType = BoolType
    def rType: SSLType = BoolType
    def resType: SSLType = BoolType
  }
  trait SymmetricOp
  trait AssociativeOp

  object OpOverloadedEq extends OverloadedBinOp{
    override def level: Int = 3
    override def pp: String = "=="
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map(
      (IntType, IntType) -> OpEq,
      (IntSetType, IntSetType) -> OpSetEq,
      (BoolType, BoolType) -> OpBoolEq,
    )

    override def default: BinOp = OpEq
  }

  object OpPlus extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "+"
    def lType: SSLType = IntType
    def rType: SSLType = IntType
    def resType: SSLType = IntType
  }
  object OpMinus extends BinOp {
    def level: Int = 4
    override def pp: String = "-"
    def lType: SSLType = IntType
    def rType: SSLType = IntType
    def resType: SSLType = IntType
  }
  object OpEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=="
    def lType: SSLType = IntType
    def rType: SSLType = IntType
  }

  object OpBoolEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=="
    def lType: SSLType = BoolType
    def rType: SSLType = BoolType
  }

  object OpLeq extends RelOp {
    def level: Int = 3
    override def pp: String = "<="
    def lType: SSLType = IntType
    def rType: SSLType = IntType
  }
  object OpLt extends RelOp {
    def level: Int = 3
    override def pp: String = "<"
    def lType: SSLType = IntType
    def rType: SSLType = IntType
  }
  object OpAnd extends LogicOp with SymmetricOp with AssociativeOp {
    def level: Int = 2
    override def pp: String = "&&"
  }
  object OpOr extends LogicOp with SymmetricOp with AssociativeOp {
    def level: Int = 1
    override def pp: String = "||"
  }
  object OpUnion extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "++"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
    def resType: SSLType = IntSetType
  }
  object OpDiff extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "--"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
    def resType: SSLType = IntSetType
  }
  object OpIn extends RelOp {
    def level: Int = 3
    override def pp: String = "in"
    def lType: SSLType = IntType
    def rType: SSLType = IntSetType
  }
  object OpSetEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=i"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
  }
  object OpSubset extends RelOp {
    def level: Int = 3
    override def pp: String = "<=i"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
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
    def eq(other: Expr, t: SSLType): Expr = t match {
      case IntSetType => BinaryExpr(OpSetEq, this, other)
      case BoolType => this <==> other
      case _ => this |=| other
    }
    def neq(other: Expr, t: SSLType): Expr = this.eq(other, t).not
    def |<=| (other: Expr): Expr = BinaryExpr(OpLeq, this, other)

    def not: Expr = UnaryExpr(OpNot, this)
    def && (other: Expr): Expr = BinaryExpr(OpAnd, this, other)
    def || (other: Expr): Expr = BinaryExpr(OpOr, this, other)
    def ==> (other: Expr): Expr = this.not || other
    def <==> (other: Expr): Expr = (this ==> other) && (other ==> this)

    def getType(gamma: Gamma): Option[SSLType]

    def resolve(gamma: Gamma, target: Option[SSLType]): Option[Gamma] = this match {
      case v@Var(_) => gamma.get(v) match {
        case Some(t) => t.supertype(target) match {
          case None => None
          case Some(t1) => Some(gamma + (v -> t1))
        }
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
      case OverloadedBinaryExpr(overloaded_op, left, right) =>
        val possible_gammas = for{
          ((lTarget, rTarget), op) <- overloaded_op.opFromTypes
          if op.resType.conformsTo(target)
          gamma1 <- left.resolve(gamma, Some(lTarget))
          gamma2 <- right.resolve(gamma1, Some(rTarget))
          is_exactly_defined = (left.getType(gamma2).contains(lTarget)
                            && right.getType(gamma2).contains(rTarget))
        } yield (gamma2, is_exactly_defined)
        val exact_gammas = possible_gammas.filter {case (_, exact) => exact}
        exact_gammas.size match{
          case 0 =>
            possible_gammas.size match{
              case 0 => None
              case 1 => Some(possible_gammas.head._1)
              case _ => BinaryExpr(overloaded_op.default, left, right).resolve(gamma, target) // Ambiguity, using default
            }
          case 1 => Some(exact_gammas.head._1)
          case _ => BinaryExpr(overloaded_op.default, left, right).resolve(gamma, target) // Ambiguity, using default
        }
      case SetLiteral(elems) =>
        if (IntSetType.conformsTo(target)) {
          elems.foldLeft[Option[Map[Var, SSLType]]](Some(gamma))((go, e) => go match {
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

    // Expression size in AST nodes
    def size: Int = this match {
      case BinaryExpr(_, l, r) => 1 + l.size + r.size
      case UnaryExpr(_, arg) => 1 + arg.size
      case SetLiteral(elems) => 1 + elems.map(_.size).sum
      case IfThenElse(cond, l, r) => 1 + cond.size + l.size + r.size
      case _ => 1
    }

    def resolveOverloading(gamma: Gamma) :Expr= this match {
      case expr: OverloadedBinaryExpr =>
        BinaryExpr(
          expr.inferConcreteOp(gamma),
          expr.left.resolveOverloading(gamma),
          expr.right.resolveOverloading(gamma))
      case Var(_)
      | BoolConst(_)
      | IntConst(_)  => this
      case UnaryExpr(op, e) => UnaryExpr(op, e.resolveOverloading(gamma))
      case BinaryExpr(op, l, r) => BinaryExpr(op, l.resolveOverloading(gamma), r.resolveOverloading(gamma))
      case SetLiteral(elems) => SetLiteral(elems.map(_.resolveOverloading(gamma)))
      case IfThenElse(c, t, e) =>IfThenElse(c.resolveOverloading(gamma),
                                            t.resolveOverloading(gamma),
                                            e.resolveOverloading(gamma))

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

    def getType(gamma: Map[Var, SSLType]): Option[SSLType] = gamma.get(this)
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

    def getType(gamma: Map[Var, SSLType]): Option[SSLType] = Some(IntType)
  }

  val NilPtr = IntConst(0)

  case class BoolConst(value: Boolean) extends Const(value) {
    def getType(gamma: Map[Var, SSLType]): Option[SSLType] = Some(BoolType)
  }



  case class BinaryExpr(op: BinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = BinaryExpr(op, left.subst(sigma), right.subst(sigma))
    override def level: Int = op.level
    override def associative: Boolean = op.isInstanceOf[AssociativeOp]
    override def pp: String = s"${left.printAtLevel(level)} ${op.pp} ${right.printAtLevel(level)}"
    def getType(gamma: Map[Var, SSLType]): Option[SSLType] = Some(op.resType)
  }

  case class OverloadedBinaryExpr(overloaded_op: OverloadedBinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = OverloadedBinaryExpr(overloaded_op, left.subst(sigma), right.subst(sigma))
    override def level: Int = overloaded_op.level
    override def associative: Boolean = overloaded_op.isInstanceOf[AssociativeOp]
    override def pp: String = s"${left.printAtLevel(level)} ${overloaded_op.pp} ${right.printAtLevel(level)}"

    def inferConcreteOp(gamma: Gamma):BinOp = {
      val lType = left.getType(gamma)
      val rType = right.getType(gamma)
      val strictly_defined_ops = for {
        ((lTarget, rTarget), op) <- overloaded_op.opFromTypes
        if (lType.contains(lTarget)|| lType.isEmpty) && (rType.contains(rTarget) || rType.isEmpty)
      } yield op
      strictly_defined_ops.size match {
        case 1 => strictly_defined_ops.head
        case n if n > 1 =>
          val op = overloaded_op.default
          if (lType.isEmpty || lType.get.conformsTo(Some(op.lType))
            && rType.isEmpty || rType.get.conformsTo(Some(op.rType))) {
            op
          } else {
            throw SynthesisException(s"Operation ${overloaded_op.pp} is ambiguous for strong typing ${(lType, rType)}" +
              s", and arguments don't conform to the default types")
          }
        case 0 =>
          val defined_ops = for {
            ((lTarget, rTarget), op) <- overloaded_op.opFromTypes
            l_ok = lType match {
              case Some(t) => t.conformsTo(Some(lTarget))
              case None => true
            }
            r_ok = rType match {
              case Some(t) => t.conformsTo(Some(rTarget))
              case None => true
            }
            if l_ok && r_ok
          } yield op
          defined_ops.size match {
            case 0 => throw SynthesisException(s"Operation ${overloaded_op.pp} is not defined for input types ${(lType, rType)}")
            case 1 => defined_ops.head
            case _ =>
              val op = overloaded_op.default
              if (lType.isEmpty || lType.get.conformsTo(Some(op.lType))
                && rType.isEmpty || rType.get.conformsTo(Some(op.rType))) {
                op
              } else {
                throw SynthesisException(s"Operation ${overloaded_op.pp} is ambiguous for weak typing ${(lType, rType)}" +
                  s", and arguments don't conform to the default types")
              }
          }
      }
    }
    override def getType(gamma: Gamma): Option[SSLType] = Some(inferConcreteOp(gamma).resType)
  }

  case class UnaryExpr(op: UnOp, arg: Expr) extends Expr {
    def subst(sigma: Map[Var, Expr]): Expr = UnaryExpr(op, arg.subst(sigma))

    override def level = 5
    override def pp: String = s"${op.pp} ${arg.printAtLevel(level)}"
    def getType(gamma: Map[Var, SSLType]): Option[SSLType] = Some(BoolType)
  }

  case class SetLiteral(elems: List[Expr]) extends Expr {
    override def pp: String = s"{${elems.map(_.pp).mkString(", ")}}"
    override def subst(sigma: Map[Var, Expr]): SetLiteral = SetLiteral(elems.map(_.subst(sigma)))
    def getType(gamma: Map[Var, SSLType]): Option[SSLType] = Some(IntSetType)
  }

  case class IfThenElse(cond: Expr, left: Expr, right: Expr) extends Expr {
    override def level: Int = 0
    override def pp: String = s"${cond.printAtLevel(level)} ? ${left.printAtLevel(level)} : ${right.printAtLevel(level)}"
    override def subst(sigma: Map[Var, Expr]): IfThenElse = IfThenElse(cond.subst(sigma), left.subst(sigma), right.subst(sigma))
    def getType(gamma: Map[Var, SSLType]): Option[SSLType] = left.getType(gamma)
  }

}




