package org.tygus.synsl.logic

import org.tygus.synsl.PrettyPrinting
import org.tygus.synsl.language.SynslType
import org.tygus.synsl.language.Expressions._


/**
  * Pure fragment of the logic
  */
trait PureFormulas {

  type Ident = String

  sealed abstract class PureFormula extends PrettyPrinting {

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
  }
  object PFalse extends PureFormula {
    override def pp: Ident = "false"
  }

  // Ф <= Ф', Ф < Ф', Ф == Ф'
  case class PLeq(left: Expr, right: Expr) extends PureFormula {
    override def pp: Ident = s"${left.pp} <= ${right.pp}"
  }
  case class PLtn(left: Expr, right: Expr) extends PureFormula {
    override def pp: Ident = s"${left.pp} < ${right.pp}"
  }
  case class PEq(left: Expr, right: Expr) extends PureFormula {
    override def pp: Ident = s"${left.pp} = ${right.pp}"
  }

  // Connectives
  case class PAnd(left: PureFormula, right: PureFormula) extends PureFormula {
    override def pp: Ident = s"(${left.pp} /\\ ${right.pp})"
  }
  case class POr(left: PureFormula, right: PureFormula) extends PureFormula {
    override def pp: Ident = s"(${left.pp} \\/ ${right.pp})"
  }
  case class PNeg(arg: PureFormula) extends PureFormula {
    override def pp: Ident = s"~~${arg.pp}"
  }

}

/**
  * Separation logic fragment
  */
trait SpatialFormulas extends PureFormulas {

  sealed abstract class SFormula extends PrettyPrinting {
    // Collect certain sub-expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
      def collector(acc: Set[R])(sigma: SFormula): Set[R] = sigma match {
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

    def canonicalize: SFormula = this

  }

  case object Emp extends SFormula {
    override def pp: Ident = "emp"
  }
  case object STrue extends SFormula {
    override def pp: Ident = "true"
  }
  case object SFalse extends SFormula {
    override def pp: Ident = "false"
  }

  // Should we support pointer arithmetics here
  case class PointsTo(id: String, offset: Int = 0, value: Expr) extends SFormula {
    override def pp: Ident = s"$id :-> ${value.pp}"
  }

  case class Sep(left: SFormula, right: SFormula) extends SFormula {
    override def pp: Ident = s"${left.pp} ** ${right.pp}"

    // TODO: Implement all machinery to work with the separating conjunections

    // Unroll to a list of non-sep formulas
    private def unroll: Seq[SFormula] = {
      val l = left match {
        case sp: Sep => sp.unroll
        case x => Seq(x)
      }
      val r = right match {
        case sp: Sep => sp.unroll
        case x => Seq(x)
      }
      l ++ r
    }

    // Bring to a canonical form
    // TODO: discuss what a canonical form should be
    override def canonicalize: SFormula = {
      val lst = this.unroll
      // Bring first all sorted points-to assertions
      val ptsSorted = lst.filter(_.isInstanceOf[PointsTo]).sortBy(p => p.asInstanceOf[PointsTo].id)
      val nonpts = lst.filterNot(_.isInstanceOf[PointsTo])

      val chunks = ptsSorted ++ nonpts
      if (chunks.isEmpty) {
        println("crap!")
      }
      assert(chunks.nonEmpty)
      if (chunks.size == 1) return chunks.head

      val rchs = chunks.reverse
      rchs.tail.foldLeft(rchs.head)((a, b) => Sep(b, a))
    }

  }

  // TODO: extend with inductive predicates

}

object Specifications extends SpatialFormulas {

  case class Assertion(phi: PureFormula, sigma: SFormula) {

    def pp: String = s"{${phi.pp} ; ${sigma.canonicalize.pp}}"

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
    * @param name    Procedure name
    * @param tpe     Procedure return type
    * @param formals parameters of the code fragment
    */
  case class Spec(pre: Assertion, post: Assertion, tpe: SynslType, name: Ident, formals: Seq[(SynslType, Var)]) {

    def pp: String = s"${pre.pp} ${tpe.pp} " +
        s"$name(${formals.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}) " +
        s"${post.pp}"

    // Universally quantified ghosts: do not take formals into the account
    def universals: Set[Var] = pre.vars -- formals.map(_._2)

    def existentials: Set[Var] = post.vars -- pre.vars

    def givenConstants: Set[PConst] = pre.collectE(_.isInstanceOf[PConst])

    def constantsInPost: Set[PConst] = post.collectE(_.isInstanceOf[PConst])

  }

}
