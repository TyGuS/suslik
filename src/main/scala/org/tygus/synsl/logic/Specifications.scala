package org.tygus.synsl.logic

import org.tygus.synsl.PrettyPrinting
import org.tygus.synsl.language.{IntType, SynslType}
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

    def getHeadHeaplet: Option[PointsTo] = this.canonicalize match {
      case Sep(left, _) => left.getHeadHeaplet
      case p@PointsTo(_, _, _) => Some(p)
      case _ => None
    }

    // TODO: This is why we need fancy SL-based tools
    def entails(other: SFormula): Boolean = this == other

    def |-(other: SFormula): Boolean = this.entails(other)
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
      assert(chunks.nonEmpty)
      if (chunks.size == 1) return chunks.head

      val rchs = chunks.reverse
      rchs.tail.foldLeft(rchs.head)((a, b) => Sep(b, a))
    }

  }

  // TODO: extend with inductive predicates

}

object Specifications extends SpatialFormulas {

  type Gamma = Seq[(SynslType, Var)]

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
  }


  /**
    * Main class for contextual Hoare-style specifications
    */
  case class Spec(pre: Assertion, post: Assertion, gamma: Gamma) {
    def ghosts: Set[Var] = pre.vars -- formals

    def formals: Set[Var] = gamma.map(_._2).toSet

    def existentials: Set[Var] = (post.vars -- ghosts) -- formals

    def givenConstants: Set[PConst] = pre.collectE(_.isInstanceOf[PConst])

    def constantsInPost: Set[PConst] = post.collectE(_.isInstanceOf[PConst])

    /**
      * Determine whether `x` is a ghost vriaable wrt. given spec and gamma
      */
    def isGhost(x: Var): Boolean = ghosts.contains(x)

    def getType(x: Var): Option[SynslType] = {
      // TODO: all ghosts are ints for now, until we descide how to infer it
      if (isGhost(x)) return Some(IntType)

      // Typed variables get the type automatically
      gamma.find(_._2 == x) match {
        case Some((t, _)) => Some(t)
        case None => None
      }
    }
  }

  /**
    * Hoare-style SL specification
    *
    * @param spec pre/postconditions and variable context
    * @param name Procedure name (optional)
    * @param tpe  Procedure return type
    */
  case class FullSpec(spec: Spec, tpe: SynslType, name: Option[Ident])
      extends PrettyPrinting {

    override def pp: String = {
      val Spec(pre, post, gamma) = spec
      s"${pre.pp} ${tpe.pp} " +
          s"$name(${gamma.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}) " +
          s"${post.pp}"
    }

  }


}
