package org.tygus.synsl.logic

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Expressions.{Expr, Var}
import org.tygus.synsl.logic.unification.SpatialUnification.tryUnify

/**
  * Utilities for spatial formulae
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait SepLogicUtils extends PureLogicUtils {

  protected def slAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SepLogicException(msg)

  /**
    * Get the heaplet satisfying the predicate
    */
  def findHeaplet(p: (Heaplet) => Boolean,
                  sigma: SFormula): Option[Heaplet] = sigma.chunks.find(p)

  def findMatchingHeaplets(pl: Heaplet => Boolean,
                           pr: (Heaplet, Heaplet) => Boolean,
                           pre: SFormula,
                           post: SFormula): Option[(Heaplet, Heaplet)] = {
    (for {hl <- pre.chunks.toStream if pl(hl)
          hr <- post.chunks.toStream if pr(hl, hr)} yield (hl, hr)).headOption
  }

  def sameLhs(hl: Heaplet): Heaplet => Boolean = hr => {
    slAssert(hl.isInstanceOf[PointsTo], s"sameLhs expected points-to chunk and got ${hl.pp}")
    val pt = hl.asInstanceOf[PointsTo]
    hr match {
      case PointsTo(y, off, _) => pt.loc == y && pt.offset == off
      case _ => false
    }
  }

  /**
    * Find the set of sub-formalas of `large` that `small` might possibly by unified with.
    */
  def findLargestMatchingHeap(small: SFormula, large: SFormula): Seq[SFormula] = {

    def findMatchingFor(h: Heaplet, stuff: Seq[Heaplet]): Seq[Heaplet] = h match {
      case Block(loc, sz) => stuff.filter {
        case Block(_, _sz) => sz == _sz
        case _ => false
      }
      case PointsTo(loc, offset, value) =>
        def hasBlockForLoc(_loc: Expr) = stuff.exists {
          case Block(_loc1, _) => _loc == _loc1
          case _ => false
        }

        stuff.filter {
          case PointsTo(_loc, _offset, _value) => offset == _offset && !hasBlockForLoc(_loc)
          case _ => false
        }
      case SApp(pred, args, tag) => stuff.filter {
        case SApp(_pred, _args, _tag) =>
          _pred == pred && args.length == _args.length && tag == _tag
        case _ => false
      }
    }

    def goFind(lil: List[Heaplet], larg: List[Heaplet], acc: List[List[Heaplet]]): List[List[Heaplet]] = lil match {
      case h :: hs => (for {
        h1 <- findMatchingFor(h, larg)
        larg1 = larg.filter(_ != h1)
        acc1 = acc.map(hs1 => h1 :: hs1)
        res <- goFind(hs, larg1, acc1)
      } yield res).toList
      case Nil => acc
    }

    goFind(small.chunks, large.chunks, List(Nil)).map(SFormula)
  }

  private def removeSingleChunk(sf1: SFormula, sf2: SFormula, p: Heaplet) = {
    val _sf1 = sf1 - p
    val _sf2 = sf2 - p
    if (_sf1.chunks.length == sf1.chunks.length - 1 &&
        _sf2.chunks.length == sf2.chunks.length - 1) Some((_sf1, _sf2, SFormula(List(p))))
    else None
  }

  private def removeSAppIgnoringTag(sf: SFormula, h: SApp) = h match {
    case SApp(p, args, _) =>
      val newChunks = sf.chunks.filterNot {
        case SApp(p1, args1, _) => p1 == p && args1 == args
        case _ => false
      }
      sf.copy(chunks = newChunks)
  }

  private def removeSAppChunk(sf1: SFormula, sf2: SFormula, s: SApp) = {
    val _sf1 = removeSAppIgnoringTag(sf1, s)
    val _sf2 = removeSAppIgnoringTag(sf2, s)
    if (_sf1.chunks.length == sf1.chunks.length - 1 &&
        _sf2.chunks.length == sf2.chunks.length - 1) Some((_sf1, _sf2, SFormula(List(s))))
    else None
  }

  /**
    */
  def findBlockRootedSubHeap(b: Block, sf: SFormula): Option[List[Heaplet]] = {
    if (!sf.chunks.contains(b)) return None
    val Block(x, sz) = b
    val ps = for {p@PointsTo(y, o, _) <- sf.chunks if x == y} yield p
    val offsets = ps.map { case PointsTo(_, o, _) => o }.sorted
    val goodChunks = offsets.size == sz && // All offsets are present
        offsets.distinct.size == offsets.size && // No repetitions
        offsets.forall(o => o < sz) // all smaller than sz
    if (goodChunks) Some(b :: ps) else None
  }


  /**
    * Removes the largest common frame from two spatial formula.
    *
    * Works trivially for points-to and SApp-like heaplets,
    * but strips off the entire array for allocated blocks!
    *
    * The `boundVars` argument is passed to ensure the correcntess of the
    *
    * The last component of the results is the chopped off subformula.
    */
  def tryRemoveCommonFrame(ft: SFormula, fs: SFormula,
                           boundVars: Set[Var]): Seq[(SFormula, SFormula, SFormula, Map[Var, Expr])] = {

    // Strip as much from the two formulas as possible,
    // and unify in the process, delivering the new substitution
    def stripper(sub: Map[Var, Expr], h: Heaplet) = h match {
      case p@PointsTo(_, _, _) => removeSingleChunk(ft, fs.subst(sub), p).map(x => (x, sub))
      case s@SApp(_, _, _) => removeSAppChunk(ft, fs.subst(sub), s).map(x => (x, sub))
      case b@Block(_, _) => removeSingleChunk(ft, fs.subst(sub), b).map(x => (x, sub)) // TODO: make me better!
    }

    for {
      t <- ft.chunksForUnifying
      s <- fs.chunksForUnifying
      sub <- tryUnify(t, s, boundVars, false)
      ((_ft, _fs, f), newSub) <- stripper(sub, t)
    } yield (_ft, _fs, f, newSub)
  }

}

case class SepLogicException(msg: String) extends SynSLException("seplog", msg)

