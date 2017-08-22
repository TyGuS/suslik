package org.tygus.synsl.logic

import org.tygus.synsl.language.{Expressions, PrimitiveType}


/**
  * Pure fragment of the logic
  */
trait PureFormulas extends Expressions {

  type Ident = String

  sealed abstract class PureFormula {

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
    override def toString: Ident = "true"
  }
  object PFalse extends PureFormula {
    override def toString: Ident = "false"
  }

  // Ф <= Ф', Ф < Ф', Ф == Ф'
  case class PLeq(left: Expr, right: Expr) extends PureFormula {
    override def toString: Ident = s"$left <= $right"
  }
  case class PLtn(left: Expr, right: Expr) extends PureFormula {
    override def toString: Ident = s"$left < $right"
  }
  case class PEq(left: Expr, right: Expr) extends PureFormula {
    override def toString: Ident = s"$left = $right"
  }

  // Connectives
  case class PAnd(left: PureFormula, right: PureFormula) extends PureFormula {
    override def toString: Ident = s"($left /\\ $right)"
  }
  case class POr(left: PureFormula, right: PureFormula) extends PureFormula {
    override def toString: Ident = s"($left \\/ $right)"
  }
  case class PNeg(arg: PureFormula) extends PureFormula {
    override def toString: Ident = s"~~$arg"
  }

}

/**
  * Separation logic fragment
  */
trait SpatialFormulas extends PureFormulas {

  sealed abstract class SpatialFormula {
    // Collect certain sub-expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
      def collector(acc: Set[R])(sigma: SpatialFormula): Set[R] = sigma match {
        case STrue => acc
        case SFalse => acc
        case Emp => acc
        case PointsTo(id, offset, value) =>
          val v = Var(id)
          val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
          acc1 ++ value.collect(p)
        case Sep(left, right) => collector(collector(acc)(left))(right)
      }
      collector(Set.empty)(this)
    }

  }

  case object Emp extends SpatialFormula {
    override def toString: Ident = "emp"
  }
  case object STrue extends SpatialFormula {
    override def toString: Ident = "true"
  }
  case object SFalse extends SpatialFormula {
    override def toString: Ident = "false"
  }

  // Should we support pointer arithmetics here
  case class PointsTo(id: String, offset: Int = 0, value: Expr) extends SpatialFormula {
    override def toString: Ident = s"$id :-> $value"
  }

  case class Sep(left: SpatialFormula, right: SpatialFormula) extends SpatialFormula {
    override def toString: Ident = s"$left ** $right"
  }

  // TODO: extend with inductive predicates

}

trait Specifications extends SpatialFormulas {

  case class Assertion(phi: PureFormula, sigma: SpatialFormula) {

    override def toString: Ident = s"{$phi ; $sigma}"

    // Get free variables
    def varsPhi: Set[Var] = phi.collectE(_.isInstanceOf[Var])
    def varsSigma: Set[Var] = sigma.collectE(_.isInstanceOf[Var])

    // Get all variables in the assertion
    def vars: Set[Var] = varsPhi ++ varsSigma

    // Collect arbitrary expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] =
      phi.collectE(p) ++ sigma.collectE(p)

    // TODO: engineer more well-formedness
  }

  /**
    * Hoare-style SL specification
    *
    * @param pre     precondition
    * @param post    postcondition
    * @param formals parameters of the code fragment
    */
  case class Spec(pre: Assertion, post: Assertion, name: Ident, formals: Seq[(PrimitiveType, Var)]) {

    override def toString: Ident =
      s"$pre $name(${formals.map { case (t, i) => s"$t $i" }.mkString(", ")}) $post"

    // Universally quantified ghosts: do not take formals into the account
    def universals: Set[Var] = pre.vars -- formals.map(_._2)

    def existentials: Set[Var] = post.vars -- pre.vars

    def givenConstants: Set[PConst] = pre.collectE(_.isInstanceOf[PConst])

    def constantsInPost: Set[PConst] = post.collectE(_.isInstanceOf[PConst])

  }

}
