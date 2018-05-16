package org.tygus.synsl.logic

import org.tygus.synsl.language._
import org.tygus.synsl.language.Expressions._

/**
  * Separation logic fragment
  */
sealed abstract class Heaplet extends PrettyPrinting with Substitutable[Heaplet] with SepLogicUtils {

  // Collect certain sub-expressions
  def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
    def collector(acc: Set[R])(h: Heaplet): Set[R] = h match {
      case PointsTo(v, offset, value) =>
        val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
        acc1 ++ value.collect(p)
      case Block(v, sz) =>
        if (p(v)) acc + v.asInstanceOf[R] else acc
      case SApp(_, args, _) => args.foldLeft(acc)((a, e) => a ++ e.collect(p))
    }

    collector(Set.empty)(this)
  }

  def vars: Set[Var] = collectE(_.isInstanceOf[Var])

  def |-(other: Heaplet): Boolean

}

/**
  * var + offset :-> value
  */
case class PointsTo(loc: Expr, offset: Int = 0, value: Expr) extends Heaplet {
  override def pp: Ident = {
    val head = if (offset <= 0) loc.pp else s"(${loc.pp} + $offset)"
    s"$head :-> ${value.pp}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet =
    PointsTo(loc.subst(sigma), offset, value.subst(sigma))

  def |-(other: Heaplet): Boolean = other match {
    case PointsTo(_loc, _offset, _value) => this.loc == _loc && this.offset == _offset && this.value == _value
    case _ => false
  }
}

/**
  * block(var, size)
  */
case class Block(loc: Expr, sz: Int) extends Heaplet {
  override def pp: Ident = {
    s"[${loc.pp}, $sz]"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    Block(loc.subst(sigma), sz)
  }

  def |-(other: Heaplet): Boolean = false
}

/**
  * Predicate application
  */
case class SApp(pred: Ident, args: Seq[Expr], tag: Option[Int] = Some(0)) extends Heaplet {
  override def pp: String = s"$pred(${args.map(_.pp).mkString(", ")})[$tag]"

  def subst(sigma: Map[Var, Expr]): Heaplet = this.copy(args = args.map(_.subst(sigma)))

  def |-(other: Heaplet): Boolean = false
}


case class SFormula(chunks: List[Heaplet]) extends PrettyPrinting with Substitutable[SFormula] {
  override def pp: Ident = if (chunks.isEmpty) "emp" else chunks.map(_.pp).mkString(" ** ")

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.map(_.subst(sigma)))

  // Collect certain sub-expressions
  def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collectE(p))
  }

  /**
    * Change tags for applications, to avoind re-applying the rule
    */
  def bumpUpSAppTags(cond: Heaplet => Boolean = _ => true): SFormula = SFormula(chunks.map {
    case a@SApp(_, _, t) if cond(a) => a.copy(tag = t.map(_ + 1))
    case x => x
  })

  def setUpSAppTags(i : Int, cond: Heaplet => Boolean = _ => true): SFormula = SFormula(chunks.map {
    case a@SApp(_, _, t) if cond(a) => a.copy(tag = Some(i))
    case x => x
  })

  def lockSAppTags(cond: Heaplet => Boolean = _ => true) : SFormula = SFormula(chunks.map {
    case a@SApp(_, _, t) if cond(a) => a.copy(tag = None)
    case x => x
  })

  def isEmp: Boolean = chunks.isEmpty

  def **(h: Heaplet): SFormula = SFormula(h :: chunks)

  def **(other: SFormula): SFormula = SFormula(chunks ++ other.chunks)

  def -(h: Heaplet): SFormula = SFormula(chunks.filterNot(elm => elm == h))

  def -(hs: Seq[Heaplet]): SFormula = {
    val hSet = hs.toSet
    SFormula(chunks.filterNot(elm => hSet.contains(elm)))
  }

  def vars: List[Var] = chunks.flatMap(_.vars)

}

