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

  def findBlockRootedSubHeap(b: Block, sf: SFormula): Option[SFormula] = {
    if (!sf.chunks.contains(b)) return None
    val Block(x, sz) = b
    if (!x.isInstanceOf[Var]) return None
    val ps = for {p@PointsTo(y, o, _) <- sf.chunks if x == y} yield p
    val offsets = ps.map { case PointsTo(_, o, _) => o }.sorted
    val goodChunks = offsets.size == sz && // All offsets are present
        offsets.distinct.size == offsets.size && // No repetitions
        offsets.forall(o => o < sz) // all smaller than sz
    if (goodChunks) Some(SFormula(b :: ps)) else None
  }

  def chunksForUnifying(f: SFormula): List[Heaplet] = {
    val blocks = f.blocks
    val apps = f.apps
    val ptss = f.ptss
    // Now remove block-dependent chunks
    val chunksToRemove = (for {
      b <- blocks
      sf <- findBlockRootedSubHeap(b, f).toList
      c <- sf.chunks
    } yield c).toSet
    val res = blocks ++ apps ++ ptss.filterNot(p => chunksToRemove.contains(p))
    res
  }

}

case class SepLogicException(msg: String) extends SynSLException("seplog", msg)

