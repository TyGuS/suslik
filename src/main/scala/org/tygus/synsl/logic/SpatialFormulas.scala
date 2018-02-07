package org.tygus.synsl.logic

import org.tygus.synsl.{PrettyPrinting, Substitutable}
import org.tygus.synsl.language.Expressions.{Expr, Var}

/**
  * Separation logic fragment
  */
trait SpatialFormulas extends PureFormulas {

  sealed abstract class Heaplet extends PrettyPrinting with Substitutable[Heaplet] {
    // Collect certain sub-expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
      def collector(acc: Set[R])(h: Heaplet): Set[R] = h match {
        case PointsTo(v, offset, value) =>
          val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
          acc1 ++ value.collect(p)
        case Block(v, sz) =>
          if (p(v)) acc + v.asInstanceOf[R] else acc
        case SApp(_, args) => args.foldLeft(acc)((a, e) => a ++ e.collect(p))
      }
      collector(Set.empty)(this)
    }

    def vars: Set[Var] = collectE(_.isInstanceOf[Var])

    // TODO: We probably need more fancy entailment at some point
    def |-(other: Heaplet): Boolean = this == other
  }

  /**
    * var + offset :-> value
    */
  case class PointsTo(id: Var, offset: Int = 0, value: Expr) extends Heaplet {
    override def pp: Ident = {
      val head = if (offset <= 0) id.pp else s"(${id.pp} + $offset)"
      s"$head :-> ${value.pp}"
    }


    def subst(x: Var, by: Expr): Heaplet = {
      assert(x != id || by.isInstanceOf[Var], s"Substitution into non-variable [${by.pp} / ${x.pp}] in points-to $pp")
      val newId = if (x == id) by.asInstanceOf[Var] else id
      PointsTo(newId, offset, value.subst(x, by))
    }
  }

  /**
    * block(var, size)
    */
  case class Block(id: Var, sz: Int) extends Heaplet {
    override def pp: Ident = {
      s"[${id.pp}, $sz]"
    }

    def subst(x: Var, by: Expr): Heaplet = {
      assert(x != id || by.isInstanceOf[Var], s"Substitution into non-variable [$by / $x] in block $pp")
      val newId = if (x == id) by.asInstanceOf[Var] else id
      Block(newId, sz)
    }
  }

  /**
    * Predicate application
    */
  case class SApp(pred: Var, args: Seq[Expr]) extends Heaplet {
    override def pp: String = s"${pred.pp}(${args.map(_.pp).mkString(", ")})"
    def subst(x: Var, by: Expr): Heaplet = SApp(pred, args.map(_.subst(x, by)))
  }


  case class SFormula(chunks: List [Heaplet]) extends PrettyPrinting with Substitutable[SFormula] {
    override def pp: Ident = if (chunks.isEmpty) "emp" else chunks.map(_.pp).mkString(" ** ")

    def subst(x: Var, by: Expr): SFormula = SFormula(chunks.map(_.subst(x, by)))

    // Collect certain sub-expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
      chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collectE(p))
    }

    def isEmp: Boolean = chunks.isEmpty

    def remove(h: Heaplet): SFormula = SFormula(chunks.filterNot(elm => elm == h))

    // TODO: implement replacement of subformula by another one
  }

  // TODO: extend with inductive predicates
}
