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

    def canonicalize(putFirst: (SFormula) => Boolean): SFormula = this

    def canon = this.canonicalize(_ => true)

    def getHeadHeaplet: Option[PointsTo] = this match {
      case Sep(left, _) => left.getHeadHeaplet
      case p@PointsTo(_, _, _) => Some(p)
      case _ => None
    }

    def replaceHeadHeaplet(hp2: PointsTo): SFormula = this match {
      case Sep(left, right) => Sep(left.replaceHeadHeaplet(hp2), right)
      case p@PointsTo(_, _, _) => hp2
      case s => s
    }

    def removeHeaplet(g: PointsTo => Boolean): SFormula = {
      val f = this match {
        case Sep(left, right) => Sep(left.removeHeaplet(g), right.removeHeaplet(g))
        case p@PointsTo(_, _, _) if g(p) => Emp
        case s => s
      }
      f.canonicalize(_ => true)
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

  case object SFalse extends SFormula {
    override def pp: Ident = "false"
    def subst(x: Var, by: Expr): SFormula = this
  }

  // Should we support pointer arithmetics here
  case class PointsTo(id: String, offset: Int = 0, value: Expr) extends SFormula {
    override def pp: Ident = s"$id :-> ${value.pp}"

    def subst(x: Var, by: Expr): SFormula = {
      // TODO: Allow substitutions into the points-to sources
      val newId = if (x.name == id) x.name else id
      val newValue = value.subst(x, by)
      PointsTo(newId, offset, newValue)
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
    override def canonicalize(putFirst: SFormula => Boolean): SFormula = {
      val lst = this.unroll
      // Bring first all sorted points-to assertions
      val ptsSorted = lst.filter(_.isInstanceOf[PointsTo]).sortBy(p => p.asInstanceOf[PointsTo].id)
      val nonpts = lst.filterNot(_.isInstanceOf[PointsTo])

      // TODO: this is hacky, please, refactor
      val first = ptsSorted.filter(putFirst)
      val second = ptsSorted.filterNot(putFirst)
      val chunks = first ++ second ++ nonpts
      assert(chunks.nonEmpty)
      if (chunks.size == 1) return chunks.head

      val rchs = chunks.reverse
      rchs.tail.foldLeft(rchs.head)((a, b) => Sep(b, a))
    }

  }

  // TODO: extend with inductive predicates

}
