package org.tygus.suslik.logic

import org.tygus.suslik.language
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.synthesis.rules.LogicalRules.findMatchingHeaplets

//trait Immutable {
//  this: Heaplet =>
//  override val isMutable = false
//  // TODO add [] around immutables when printing
//
//  // TODO fix resolve so that it carries over immutability 
//}

/*
object MTag extends Enumeration {
  type MutabilityTag = Either[Value, Integer]
  val Mut, Imm, Abs, U = Value
*/

  sealed /*case class*/ trait MTag

  case object Mut extends MTag
  case object Imm extends MTag
  case object Abs extends MTag
  case class U(tag : Integer) extends MTag


  object MTag {

    def checkLists(s1 : Option[List[MTag]], s2: Option[List[MTag]]) : Boolean = (s1, s2) match {
      case (Some(a), Some(b)) => a.zip(b).forall({ case (a,b) => (a,b) match {
        //case (_, U(m)) => true
        //case (U(n), _) => true
        case (x, y) => x == y
        case (_, _) => false} })
      case (None, None) => true
      case _ => false
    }

// TODO what's the correct way?
  // need to reduce I to A
  def pre(t1: MTag, t2: MTag): Boolean = (t1, t2) match {
    //case (_, U(n)) => true // TODO [Immutability] not sure if this is always the case. can you unify U tags? or do you always expand? you should be expanding...
    //case (U(n), _) => true // TODO [Immutability] not sure if this is always the case
    case (Mut, _) => true
    case (_, Abs) => true
    case (x, y) if x == y => true
    case _ => false
  }

  def lub(t1: MTag, t2: MTag) = (t1, t2) match {
    case (Mut, x) => x
    case (x, Mut) => x
    case (_, Abs) => Abs
    case (Abs, _) => Abs
    case (x, _) => x
  }

  def glb(t1: MTag, t2: MTag) = (t1, t2) match {
    case (Mut, _) => Mut
    case (_, Mut) => Mut
    case (x, Abs) => x
    case (Abs, x) => x
    case (x, _) => x
  }

  def residue(have: MTag, need: MTag) : MTag = (have, need) match {
//    case (Imm, Imm) => Imm
//    case (x, y) if x == y => Abs
//    case (_, Abs) => have
//    case (Mut, Imm) => Mut

    case (Mut, Mut) => Abs
    case (Mut, _) => Mut // weird case of Mut, Imm
    //case (Mut, Imm) => Abs // proper calculus
    case (Imm, Imm) => Imm
    case (x, Abs) => x
    case _ => Abs // disallowed cases, e.g. Imm, Mut TODO [Immutability]
  }

  def isMutable(tag: MTag): Boolean = tag == Mut
  def isImutable(tag: MTag): Boolean = tag == Imm
  def isAbsent(tag: MTag): Boolean = tag == Abs
  def isNumeric(tag: MTag): Boolean = tag.isInstanceOf[U]

}

/**
  * Separation logic fragment
  */
sealed abstract class Heaplet extends PrettyPrinting with Substitutable[Heaplet] with SepLogicUtils {
  
  def mut: MTag

  def isMutable: Boolean = MTag.isMutable(mut)
  def isImmutable: Boolean = MTag.isImutable(mut)
  def isAbsent: Boolean = MTag.isAbsent(mut)
  def isNumeric: Boolean = MTag.isNumeric(mut)
  def changeMut(mut : MTag) : Heaplet

  def makeUnknown(numberTag : Integer): Heaplet

  def mkImmutable: Heaplet

  //  def mkImmutable(): this.type = {
  //    mut = false
  //    this
  //  }
  //
  //  def mkMutable(): this.type = {
  //    mut = true
  //    this
  //  }
  //  
  //  def isMutable: Boolean = mut

  def resolveOverloading(gamma: Gamma): Heaplet

  // Collect certain sub-expressions
  def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
    def collector(acc: Set[R])(h: Heaplet): Set[R] = h match {
      case PointsTo(v, offset, value, _) =>
        val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
        acc1 ++ value.collect(p)
      case Block(v, sz, _) =>
        if (p(v)) acc + v.asInstanceOf[R] else acc
      case SApp(_, args, _, _, _) => args.foldLeft(acc)((a, e) => a ++ e.collect(p))
    }

    collector(Set.empty)(this)
  }

  def vars: Set[Var] = collectE(_.isInstanceOf[Var])

  def |-(other: Heaplet): Boolean

  def resolve(gamma: Gamma, env: Environment): Option[Gamma]

  def lhsVars: Set[Var]

  def rank: Int

  def adjustTag(f: Option[Int] => Option[Int]): Heaplet = this

  def eqModTags(other: Heaplet): Boolean = {
    this.adjustTag(_ => None) == other.adjustTag(_ => None)
  }

  // Size of the heaplet (in AST nodes)
  def size: Int = this match {
    case PointsTo(loc, _, value, _) => 1 + loc.size + value.size
    case Block(loc, _, _) => 1 + loc.size
    case SApp(_, args, _, _, _) => args.map(_.size).sum
  }

}

/**
  * var + offset :-> value
  */
case class PointsTo(loc: Expr, offset: Int = 0, value: Expr,
                    mut: MTag = Mut) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): PointsTo = {
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma))
  }

  override def pp: Ident = {
    val head = if (offset <= 0) loc.pp else s"(${loc.pp} + $offset)"
    val overall = s"$head :-> ${value.pp}"
    if (isImmutable) s"[$overall]"
    else if (isAbsent) s"[$overall]@A"
    else if (isNumeric) s"[$overall]@${mut.asInstanceOf[U].tag}"
    else overall
  }

  def subst(sigma: Map[Var, Expr]): Heaplet =
    PointsTo(loc.subst(sigma), offset, value.subst(sigma), mut)

  // TODO [Immutability] Take that partial order for mutability tags into the account
  def |-(other: Heaplet): Boolean = other match {
    case PointsTo(_loc, _offset, _value, _mut) =>
      this.loc == _loc && this.offset == _offset && this.value == _value &&
        this.mut == _mut
    case _ => false
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(IntType))
    } yield gamma2
  }

  def rank: Int = 2

  override def mkImmutable = this.copy(mut = Imm)

  override def makeUnknown(numberTag: Integer): Heaplet = this.copy(mut = U(numberTag))

  override def lhsVars: Set[Var] = loc match {
    case elems: Var => Set[Var](elems)
    case _ => Set.empty[Var]
  }

  override def changeMut(mut : MTag): Heaplet = this.copy(mut = mut)
}

/**
  * block(var, size)
  */
case class Block(loc: Expr, sz: Int, mut: MTag = Mut) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma))

  override def pp: Ident = {
    val overall = s"[${loc.pp}, $sz]"
    if (isImmutable) s"[$overall]"
    else if (isAbsent) s"[$overall]@A"
    else if (isNumeric) s"[$overall]@${mut.asInstanceOf[U].tag}"
    //else if (mut == MTag.U) s"[$overall]@${mut.tag}"
    else overall
  }

  // TODO no way there isn't a better way of extending the immutable behaviour
  def subst(sigma: Map[Var, Expr]): Heaplet = Block(loc.subst(sigma), sz, mut)

  override def mkImmutable = this.copy(mut = Imm)
  override def makeUnknown(numberTag: Integer): Heaplet = this.copy(mut = U(numberTag))

  def |-(other: Heaplet): Boolean = false

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = loc.resolve(gamma, Some(LocType))

  def rank: Int = 1

  override def lhsVars: Set[Var] = loc match {
    case elems: Var => Set[Var](elems)
    case _ => Set.empty[Var]
  }

  override def changeMut(mut : MTag): Heaplet = this.copy(mut = mut)
}

/**
  * Predicate application
  */
case class SApp(pred: Ident, args: Seq[PFormula], tag: Option[Int] = Some(0), mut: MTag = Mut, submut: Option[List[MTag]] = None) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(args = args.map(_.resolveOverloading(gamma)), submut = submut)

  override def pp: String = {
    val ppTag: Option[Int] => String = {
      case None => "[-]" // "[\uD83D\uDD12]" // "locked"
      case Some(0) => "" // Default tag
      case Some(t) => s"[$t]"
    }
    val overall = s"$pred(${args.map(_.pp).mkString(", ")})${ppTag(tag)}"
    if (isImmutable) s"[$overall]"
    else if (isAbsent) s"[$overall]@A"
    else if (submut.nonEmpty) s"$overall[${submut.get}]"
    else overall
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = this.copy(args = args.map(_.subst(sigma)), submut = submut)

  override def mkImmutable = this.copy(mut = Imm, submut = submut)

  override def changeMut(mut : MTag): Heaplet = this.copy(mut = mut)

  override def makeUnknown(numberTag: Integer): Heaplet = this.copy(mut = U(numberTag))

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

  def rank: Int = 0

  override def lhsVars: Set[Var] = args.foldLeft[Set[Var]](Set.empty[Var])((acc: Set[Var], arg: Expr) => arg match {
    case elems: Var => acc ++ Set[Var](elems)
    case _ => acc
  })

  // An application is absent also if all its constituents are absent
//  override def isAbsent: Boolean = {
//    if (submut.nonEmpty) false
//    val sms : List[MTag] = submut.get
//    mut == Abs || sms.forall(m => MTag.isAbsent(m))
//  }

  override def adjustTag(f: Option[Int] => Option[Int]): Heaplet =
    this.copy(tag = f(this.tag), submut = submut)

  def applyFineGrainedTags(hs : List[Heaplet]) : List[Heaplet] = {
    submut match {
      case Some(muts) => {
        if (muts.length < hs.length) {
          // TODO [Immutability] should really fail
        } else {
          val perms = muts
        }

        // what is it tagged with?
        // get the tag of U
        // just compare to predicate...
        hs.map {
          case SApp(a, b, c, d, e) => SApp(a, b, c, d, submut) // replace list
          case h => h.mut match {
            case U(n: Integer) => h.changeMut(muts(n))
            case _ => h
          } // TODO [Immutability] relies on starting with 0, need to reinforce it?
        }
      }
      // if None, then just treat as mut and keep going
      case None => hs.map(h => if (h.isNumeric) { h.changeMut(mut) } else { h })//copy(submut = Some((0 to hs.length).map(_ => Mut).toList)).applyFineGrainedTags(hs)
    }
  }
}


case class SFormula(chunks: List[Heaplet]) extends PrettyPrinting with Substitutable[SFormula] {
  // TODO immutable
  def resolveOverloading(gamma: Gamma): SFormula = {
    this.copy(chunks = chunks.map(_.resolveOverloading(gamma)))
  }

  override def pp: Ident = if (chunks.isEmpty) "emp" else chunks.map(_.pp).mkString(" ** ")

  // Changing it here is the wrong approach. I need to change it when it's created...
  def blocks: List[Block] = for (b@Block(_, _, _) <- chunks) yield b

  def apps: List[SApp] = for (b@SApp(_, _, _, _, _) <- chunks) yield b

  def ptss: List[PointsTo] = for (b@PointsTo(_, _, _, _) <- chunks) yield b

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.map(_.subst(sigma)))

  def replace(original: Heaplet, fresh: Heaplet) : SFormula =
    copy((fresh :: chunks) diff List(original))

  // Collect certain sub-expressions
  def collectE[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collectE(p))
  }

  /**
    * Change tags for applications, to avoind re-applying the rule
    */
  def bumpUpSAppTags(cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(t => t.map(_ + 1)) else h))

  def setUpSAppTags(i: Int, cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(_ => Some(i)) else h))

  def moveToLevel2(cond: Heaplet => Boolean = _ => true): SFormula =
    setUpSAppTags(2, cond)

  def lockSAppTags(cond: Heaplet => Boolean = _ => true): SFormula =
    SFormula(chunks.map(h => if (cond(h)) h.adjustTag(_ => None) else h))

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

  // TODO does immutability matter?
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

