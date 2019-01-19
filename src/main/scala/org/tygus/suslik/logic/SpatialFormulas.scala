package org.tygus.suslik.logic

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.synthesis.rules.LogicalRules.findMatchingHeaplets

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

  def resolve(gamma: Gamma, env: Environment): Option[Gamma]

  def rank: Int

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

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolveTypes(gamma, Some(LocType))
      gamma2 <- value.resolveTypes(gamma1, Some(IntType))
    } yield gamma2
  }

  def rank: Int = 2
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

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = loc.resolveTypes(gamma, Some(LocType))

  def rank: Int = 1
}

/**
  * Predicate application
  */
case class SApp(pred: Ident, args: Seq[Expr], tag: Option[Int] = Some(0)) extends Heaplet {
  override def pp: String = {
    val ppTag : Option[Int] => String = {
      case None => "[-]" // "[\uD83D\uDD12]" // "locked"
      case Some(0) => "" // Default tag
      case Some(t) => s"[$t]"
    }
    s"$pred(${args.map(_.pp).mkString(", ")})${ppTag(tag)}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = this.copy(args = args.map(_.subst(sigma)))

  def |-(other: Heaplet): Boolean = false

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    if (!(env.predicates contains  pred)){
      throw SynthesisException( s"predicate $pred is undefined")
    }
    val formals = env.predicates(pred).params

    if (formals.length == args.length) {
      (formals, args).zipped.foldLeft[Option[Gamma]](Some(gamma))
      { case (go, (formal, actual)) => go match {
              case None => None
              case Some(g) => actual.resolveTypes(g, Some(formal._1))
            }}
    } else None
  }

  def rank: Int = 0

  override def adjustTag(f: Option[Int] => Option[Int]): Heaplet = this.copy(tag = f(this.tag))
}


case class SFormula(chunks: List[Heaplet]) extends PrettyPrinting with Substitutable[SFormula] {
  override def pp: Ident = if (chunks.isEmpty) "emp" else chunks.map(_.pp).mkString(" ** ")

  def blocks: List[Block] = for (b@Block(_, _) <- chunks) yield b

  def apps: List[SApp] = for (b@SApp(_, _, _) <- chunks) yield b

  def ptss: List[PointsTo] = for (b@PointsTo(_, _, _) <- chunks) yield b

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.map(_.subst(sigma)))

  // Collect certain sub-expressions
  def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collectE(p))
  }

  /**
    * Change tags for applications, to avoind re-applying the rule
    */
  def bumpUpSAppTags(cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(t => t.map(_ + 1)) else h ) )

  def setUpSAppTags(i: Int, cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(_ => Some(i)) else h ) )

  def moveToLevel2(cond: Heaplet => Boolean = _ => true): SFormula =
    setUpSAppTags(2, cond)

  def lockSAppTags(cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(_ => None) else h ) )

  def isEmp: Boolean = chunks.isEmpty

  def **(h: Heaplet): SFormula = SFormula(h :: chunks)

  def **(other: SFormula): SFormula = SFormula(chunks ++ other.chunks)

  def -(h: Heaplet): SFormula = {
    val cnt = chunks.count(_ == h)
    // Remove just once!
    SFormula(chunks.filterNot(elm => elm == h) ++ (for (i <- 0 to (cnt - 2)) yield h))
  }

  def -(hs: Seq[Heaplet]): SFormula = {
    val hSet = hs.toSet
    SFormula(chunks.filterNot(elm => hSet.contains(elm)))
  }

  def vars: List[Var] = chunks.flatMap(_.vars)

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
      case Some((l, r)) => 1 + (this - l).similarity(other - r)
    }
  }

  // How many heaplets are different between the two formulas?
  def distance(other: SFormula): Int = {
    def isMatch(l: Heaplet, r: Heaplet): Boolean = l.eqModTags(r)

    findMatchingHeaplets(_ => true, isMatch, this, other) match {
      case None => this.chunks.length + other.chunks.length
      case Some((l, r)) => (this - l).distance(other - r)
    }
  }

  // Size of the formula (in AST nodes)
  def size: Int = chunks.map(_.size).sum
}

