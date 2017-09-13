package org.tygus.synsl.logic

import org.tygus.synsl.{PrettyPrinting, Substitutable}
import org.tygus.synsl.language.Expressions.{Expr, Var}

/**
  * Separation logic fragment
  */
trait SpatialFormulas extends PureFormulas {

  sealed abstract class SFormula extends PrettyPrinting with Substitutable[SFormula] {
    // Collect certain sub-expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
      def collector(acc: Set[R])(sigma: SFormula): Set[R] = sigma match {
        case SApp(_, args) => args.foldLeft(acc)((a, e) => a ++ e.collect(p))
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

    // Find subformula
    def findSubFormula(p: (SFormula) => Boolean): Set[SFormula] = {
      def collector(acc: Set[SFormula])(sigma: SFormula): Set[SFormula] =
        sigma match {
          case s@(Emp | STrue | SFalse | PointsTo(_, _, _)) if p(s) => acc + s
          case s@Sep(left, right) =>
            val acc1 = if (p(s)) acc + s else acc
            collector(collector(acc)(left))(right)
          case _ => acc
        }
      collector(Set.empty)(this)
    }

    // Find and replace sub-formula
    def findReplace(p: (SFormula) => Boolean, target: SFormula): SFormula = {
      def rep(sigma: SFormula): SFormula = sigma match {
        case s@(Emp
                | STrue
                | SFalse
                | PointsTo(_, _, _)
                | SApp(_, _)) => if (p(s)) target else s
        case s@Sep(left, right) => if (p(s)) target else Sep(rep(left), rep(right))
      }
      rep(this)
    }

    def isEmp: Boolean = this == Emp

    // simplify
    def simpl: SFormula = {
      def sim(sigma: SFormula): SFormula = sigma match {
        case s@(Emp
                | STrue
                | SFalse
                | PointsTo(_, _, _)
                | SApp(_, _)) => s
        case s@Sep(left, right) =>
          if (left.isEmp) sim(right)
          else if (right.isEmp) sim(left)
          else Sep(sim(left), sim(right))
      }
      sim(this)
    }


    // TODO: implement replacement of subformula by another one


    def canonicalize: SFormula = this

    def getHeadHeaplet: Option[PointsTo] = this match {
      case Sep(left, _) => left.getHeadHeaplet
      case p@PointsTo(_, _, _) => Some(p)
      case _ => None
    }

    /*
        private def replaceHeadHeaplet(hp2: PointsTo): SFormula = this match {
          case Sep(left, right) => Sep(left.replaceHeadHeaplet(hp2), right)
          case p@PointsTo(_, _, _) => hp2
          case s => s
        }
    */

    def removeSubformula(g: SFormula => Boolean): SFormula = this match {
      case s@Sep(left, right) =>
        if (g(s)) Emp else Sep(left.removeSubformula(g), right.removeSubformula(g)).simpl
      case s => if (g(s)) Emp else s
    }

    // TODO: This is why we need fancy SL-based tools
    def entails(other: SFormula): Boolean = this == other

    def |-(other: SFormula): Boolean = this.entails(other)
  }

  case object Emp extends SFormula {
    override def pp: Ident = "emp"
    def subst(x: Var, by: Expr): SFormula = this
  }

  case object STrue extends SFormula {
    override def pp: Ident = "true"
    def subst(x: Var, by: Expr): SFormula = this
  }

  /**
    * Predicate application
    */
  case class SApp(pred: Var, args: Seq[Expr]) extends SFormula {
    override def pp: String = s"${pred.pp}(${args.map(_.pp).mkString(", ")})"
    def subst(x: Var, by: Expr): SFormula = SApp(pred, args.map(_.subst(x, by)))
  }

  case object SFalse extends SFormula {
    override def pp: Ident = "false"
    def subst(x: Var, by: Expr): SFormula = this
  }

  // Should we support pointer arithmetics here
  case class PointsTo(id: String, offset: Int = 0, value: Expr) extends SFormula {
    override def pp: Ident = {
      val head = if (offset <= 0) id else s"($id + $offset)"
      s"$head :-> ${value.pp}"
    }


    def subst(x: Var, by: Expr): SFormula = {
      // TODO: Allow substitutions into the points-to sources
      val newId = if (x.name == id && by.isInstanceOf[Var]) by.asInstanceOf[Var].name else id
      PointsTo(newId, offset, value.subst(x, by))
    }
  }

  case class Sep(left: SFormula, right: SFormula) extends SFormula {
    override def pp: Ident = s"${left.pp} ** ${right.pp}"

    def subst(x: Var, by: Expr): SFormula = Sep(left.subst(x, by), right.subst(x, by))

    // Unroll to a list of non-sep formulas
    private def unroll: Seq[SFormula] = {
      val l = left match {
        case sp: Sep => sp.unroll
        case Emp => Seq()
        case x => Seq(x)
      }
      val r = right match {
        case sp: Sep => sp.unroll
        case Emp => Seq()
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
      rchs.tail.foldLeft(rchs.head)((a, b) => Sep(b, a)).simpl
    }

  }

  // TODO: extend with inductive predicates

}
