package org.tygus.synsl.synthesis

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.logic._

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */
trait RuleUtils {


  ////////////////////////////////////////////////////////////////
  //          Utilities for pure formulae
  ////////////////////////////////////////////////////////////////

  def simplify(phi: PFormula): PFormula = phi match {
    case p@(PTrue | PFalse) => p
    case p@PLeq(left, right) => p // TODO: Improve this
    case p@PLtn(left, right) => p // TODO: Improve this
    case p@PEq(left, right) => p // TODO: Improve this

    //  The recursive cases
    case PAnd(left, right) => PAnd(simplify(left), simplify(right))
    case POr(left, right) => POr(simplify(left), simplify(right))

    //  Classical logic stuff and de Morgan
    case PNeg(PNeg(arg)) => simplify(arg)
    case PNeg(PAnd(left, right)) => POr(simplify(PNeg(left)), simplify(PNeg(right)))
    case PNeg(POr(left, right)) => PAnd(simplify(PNeg(left)), simplify(PNeg(right)))
    case PNeg(PTrue) => PFalse
    case PNeg(PFalse) => PTrue
    case PNeg(arg) => PNeg(simplify(arg))
  }

  def isAtomicExpr(e: Expr): Boolean = e match {
    case Var(name) => true
    case PConst(value) => true
    case _ => false
  }

  def isAtomicPFormula(phi: PFormula): Boolean = phi match {
    case PTrue | PFalse => true
    case PEq(e1, e2) => isAtomicExpr(e1) && isAtomicExpr(e2)
    case PNeg(PEq(e1, e2)) => isAtomicExpr(e1) && isAtomicExpr(e2)
    case _ => false
  }

  def isSimpleConjunction(atom: PFormula => Boolean)(pf: PFormula): Boolean = {

    def check(phi: PFormula): Boolean = phi match {
      case PLeq(_, _) | PLtn(_, _) | POr(_, _) => false
      case PAnd(left, right) => check(left) && check(right)
      case p => isAtomicPFormula(p)
    }

    check(simplify(pf))
  }


  ////////////////////////////////////////////////////////////////
  //          Utilities for spatial formulae
  ////////////////////////////////////////////////////////////////

  /**
    * Get the heaplet satisfying the predicate
    */
  def findHeaplet(p: (Heaplet) => Boolean,
                  sigma: SFormula): Option[Heaplet] = {
    sigma.chunks.find(p)
  }

  def findMatchingHeaplets(pl: Heaplet => Boolean,
                           pr: (Heaplet, Heaplet) => Boolean,
                           pre: SFormula,
                           post: SFormula): Option[(Heaplet, Heaplet)]
  = {
    (for {hl <- pre.chunks.toStream if pl(hl)
          hr <- post.chunks.toStream if pr(hl, hr)} yield (hl, hr)).headOption
  }

  def sameLhs(hl: Heaplet): Heaplet => Boolean = hr => {
    assert(hl.isInstanceOf[PointsTo], s"sameLhs expected points-to chunk and got ${hl.pp}")
    val pt = hl.asInstanceOf[PointsTo]
    hr match {
      case PointsTo(y, off, _) => pt.id == y && pt.offset == off
      case _ => false
    }
  }
}
