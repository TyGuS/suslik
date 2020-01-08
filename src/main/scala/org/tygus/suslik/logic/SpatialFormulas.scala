package org.tygus.suslik.logic

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.synthesis.rules.LogicalRules.findMatchingHeaplets

/**
  * Separation logic fragment
  */
sealed abstract class Heaplet extends PrettyPrinting with HasExpressions[Heaplet] with Ordered[Heaplet] with SepLogicUtils {

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    def collector(acc: Set[R])(h: Heaplet): Set[R] = h match {
      case PointsTo(v, offset, value) =>
        val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
        acc1 ++ value.collect(p)
      case Block(v, _) =>
        if (p(v)) acc + v.asInstanceOf[R] else acc
      case SApp(_, args, _) => args.foldLeft(acc)((a, e) => a ++ e.collect(p))
    }

    collector(Set.empty)(this)
  }

  def compare(that: Heaplet): Int = this.pp.compare(that.pp)

  def |-(other: Heaplet): Boolean

  def resolve(gamma: Gamma, env: Environment): Option[Gamma]

  def adjustTag(f: Option[Int] => Option[Int]): Heaplet = this

  def eqModTags(other: Heaplet): Boolean = {
    this.adjustTag(_ => None) == other.adjustTag(_ => None)
  }

  // Size of the heaplet (in AST nodes)
  def size: Int = this match {
    case PointsTo(loc, _, value) => 1 + loc.size + value.size
    case Block(loc, _) => 1 + loc.size
    case SApp(_, args, _) => args.map(_.size).sum
  }

  def cost: Int = this match {
    case PointsTo(_, _, _) => 0
    case Block(_, _) => 0
    case SApp(_, _, None) => 3
    case SApp(_, _, Some(n)) => n
    //    case PointsTo(_, _, _) => 1
    //    case Block(_, _) => 1
    //    case SApp(_, _, _) => 10
  }

}

/**
  * var + offset :-> value
  */
case class PointsTo(loc: Expr, offset: Int = 0, value: Expr) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma))

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

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(IntType))
    } yield gamma2
  }
}

/**
  * block(var, size)
  */
case class Block(loc: Expr, sz: Int) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(loc = loc.resolveOverloading(gamma))

  override def pp: Ident = {
    s"[${loc.pp}, $sz]"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    Block(loc.subst(sigma), sz)
  }

  def |-(other: Heaplet): Boolean = false

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = loc.resolve(gamma, Some(LocType))
}

/**
  * Predicate application
  */
case class SApp(pred: Ident, args: Seq[Expr], tag: Option[Int] = Some(0)) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(args = args.map(_.resolveOverloading(gamma)))

  override def pp: String = {
    val ppTag: Option[Int] => String = {
      case None => "[-]" // "[\uD83D\uDD12]" // "locked"
      case Some(0) => "" // Default tag
      case Some(t) => s"[$t]"
    }
    s"$pred(${args.map(_.pp).mkString(", ")})${ppTag(tag)}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = this.copy(args = args.map(_.subst(sigma)))

  def |-(other: Heaplet): Boolean = false

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    if (!(env.predicates contains pred)) {
      throw SynthesisException(s"predicate $pred is undefined")
    }
    val formals = env.predicates(pred).params

    if (formals.length == args.length) {
      (formals, args).zipped.foldLeft[Option[Gamma]](Some(gamma)) { case (go, (formal, actual)) => go match {
        case None => None
        case Some(g) => actual.resolve(g, Some(formal._1))
      }
      }
    } else None
  }

  override def adjustTag(f: Option[Int] => Option[Int]): Heaplet = this.copy(tag = f(this.tag))
}


case class SFormula(chunks: List[Heaplet]) extends PrettyPrinting with HasExpressions[SFormula] {
  def resolveOverloading(gamma: Gamma): SFormula = {
    this.copy(chunks = chunks.map(_.resolveOverloading(gamma)))
  }

  override def pp: Ident = if (chunks.isEmpty) "emp" else {
    def pt(l: List[Heaplet]) = l.map(_.pp).sortBy(x => x)

    val c1 = chunks.filter(_.isInstanceOf[PointsTo])
    val c2 = chunks.filter(_.isInstanceOf[SApp])
    val c3 = chunks.filter(x => !x.isInstanceOf[PointsTo] && !x.isInstanceOf[SApp])
    List(c1, c2, c3).flatMap(pt).mkString(" ** ")
  }

  def blocks: List[Block] = for (b@Block(_, _) <- chunks) yield b

  def apps: List[SApp] = for (b@SApp(_, _, _) <- chunks) yield b

  def ptss: List[PointsTo] = for (b@PointsTo(_, _, _) <- chunks) yield b

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.map(_.subst(sigma)))

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collect(p))
  }

  /**
    * Change tags for applications, to avoid re-applying the rule
    */
  def bumpUpSAppTags(cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(t => t.map(_ + 1)) else h))

  def setUpSAppTags(i: Int, cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(_ => Some(i)) else h))

  def setToNegative(cond: Heaplet => Boolean = _ => true): SFormula =
    setUpSAppTags(-1, cond)

  def lockSAppTags(cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(_ => None) else h))

  def isEmp: Boolean = chunks.isEmpty

  // Add h to chunks (multiset semantics)
  def **(h: Heaplet): SFormula = SFormula(h :: chunks)

  // Add all chunks from other (multiset semantics)
  def **(other: SFormula): SFormula = SFormula(chunks ++ other.chunks)

  // Remove h from this formula (multiset semantics)
  def -(h: Heaplet): SFormula = SFormula(chunks.diff(List(h)))

  // Remove all chunks present in other (multiset semantics)
  def -(other: SFormula): SFormula = SFormula(chunks.diff(other.chunks))

  // Add chunks from other (set semantics)
  def +(other: SFormula): SFormula = SFormula((chunks ++ other.chunks).distinct)

  def disjoint(other: SFormula): Boolean = chunks.intersect(other.chunks).isEmpty

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    chunks.foldLeft[Option[Map[Var, SSLType]]](Some(gamma))((go, h) => go match {
      case None => None
      case Some(g) => h.resolve(g, env)
    })
  }

  // How many heaplets do the two formulas have in common?
  def similarity(other: SFormula): Int = {
    def isMatch(l: Heaplet, r: Heaplet): Boolean = l.eqModTags(r)

    findMatchingHeaplets(_ => true, isMatch, this, other) match {
      case None => 0
      case Some((l, r)) => l.cost + (this - l).similarity(other - r)
    }
  }

  def is_subheap_of(other: SFormula): Boolean = {
    similarity(other) == this.chunks.length
  }

  def replace(what: SFormula, replacement: SFormula): SFormula = {
    (this - what) ** replacement
  }

  // Size of the formula (in AST nodes)
  def size: Int = chunks.map(_.size).sum

  def cost: Int = chunks.map(_.cost).sum

  //  def cost: Int = chunks.foldLeft(0)((m, c) => m.max(c.cost))
}


