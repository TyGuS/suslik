package org.tygus.suslik.logic.unification

import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.logic.{SFormula, _}
import org.tygus.suslik.logic.Specifications._

/**
  * @author Ilya Sergey
  */
object SpatialUnification extends UnificationBase {

  type UAtom = Heaplet

  val precise: Boolean = true


  def tryUnify(target: UAtom, source: UAtom, nonFreeInSource: Set[Var]): Seq[Subst] =
    tryUnify(target, source, nonFreeInSource, tagsMatter = false)

  /**
    * Tries to unify two heaplets `target` and `source`, assuming `source` has
    * variables that are either free or in `nonFreeInSource`.
    *
    * If successful, returns a substitution from `source`'tFrame fresh variables to `target`'tFrame variables
    */
  def tryUnify(target: UAtom, source: UAtom,
               nonFreeInSource: Set[Var],
               // Take the application level tags into the account
               // should be ignored when used from the *-intro rule
               tagsMatter: Boolean = true): Seq[Subst] = {
    assert(target.vars.forall(nonFreeInSource.contains), s"Not all variables of ${target.pp} are in $nonFreeInSource")
    (target, source) match {
      case (PointsTo(x@Var(_), o1, y), PointsTo(a@Var(_), o2, b)) =>
        if (o1 != o2) Nil else {
          assert(nonFreeInSource.contains(x))
          assert(y.vars.forall(nonFreeInSource.contains))
          val sbst = for {
            m1 <- genSubst(x, a, nonFreeInSource)
            _v2 = b.subst(m1)
            m2 <- genSubst(y, _v2, nonFreeInSource)
          } yield {
            assertNoOverlap(m1, m2)
            m1 ++ m2
          }
          sbst.toList
        }
      case (Block(x1@Var(_), s1), Block(x2@Var(_), s2)) =>
        if (s1 != s2) Nil else {
          assert(nonFreeInSource.contains(x1))
          genSubst(x1, x2, nonFreeInSource).toList
        }
      case (SApp(p1, es1, targetTag), SApp(p2, es2, sourceTag)) =>
        // Only unify predicates with variables as arguments
        // if es2.forall(_.isInstanceOf[Var])

        if (p1 != p2 || es1.size != es2.size ||
            (targetTag != sourceTag && tagsMatter)) Nil

        else {
          val pairs = es1.zip(es2)
          // Collect the mapping from the predicate parameters
          pairs.foldLeft(Some(Map.empty): Option[Subst]) {
            case (opt, (x1, x2)) => opt match {
              case None => None
              case Some(acc) =>
                genSubst(x1, x2, nonFreeInSource) match {
                  case Some(sbst) =>
                    assertNoOverlap(acc, sbst)
                    Some(acc ++ sbst)
                  case None => None
                }
            }
          }.toList
        }
      case _ => Nil
    }
  }


  /**
    * Check that two lists of heaplets have a chance to be unified
    */
  protected def checkShapesMatch(cs1: List[UAtom], cs2: List[UAtom]): Boolean = {
    val (ps1, ps2) = (cs1.filter(_.isInstanceOf[PointsTo]), cs2.filter(_.isInstanceOf[PointsTo]))
    val (bs1, bs2) = (cs1.filter(_.isInstanceOf[Block]), cs2.filter(_.isInstanceOf[Block]))
    val (as1, as2) = (cs1.filter(_.isInstanceOf[SApp]), cs2.filter(_.isInstanceOf[SApp]))

    // Check sizes
    if (ps1.size != ps2.size) return false
    if (bs1.size != bs2.size) return false
    if (as1.size != as2.size) return false

    // Check matching blocks
    val checkMatchingBlocks = (bs1: List[Heaplet], bs2: List[Heaplet]) =>
      bs1.forall {
        case Block(_, s1) => bs2.exists { case Block(_, s2) => s1 == s2; case _ => false }
        case _ => false
      }

    if (!checkMatchingBlocks(bs1, bs2) || !checkMatchingBlocks(bs2, bs1)) return false

    // Check matching blocks
    val checkMatchingApps = (as1: List[Heaplet], as2: List[Heaplet]) =>
      as1.forall {
        case SApp(x1, xs1, _) =>
          as2.exists { case SApp(x2, xs2, _) => x1 == x2 && xs1.size == xs2.size; case _ => false }
        case _ => false
      }
    if (!checkMatchingApps(as1, as2) || !checkMatchingApps(as2, as1)) return false

    true
  }


  protected def extractChunks(goal: UnificationGoal): List[UAtom] = goal.formula.sigma.chunks

  ///////////////////////////////////////////////////////////////////
  // Supporting Star-Frame
  ///////////////////////////////////////////////////////////////////

  sealed case class FrameChoppingResult(sRemaining: SFormula, sFrame: SFormula,
                                        tRemaining: SFormula, tFrame: SFormula,
                                        sub: Subst)

  private def removeSingleChunk(source: SFormula, target: SFormula, p: Heaplet, sub: Subst) = {
    val _tr = target - p
    val _sr = source.subst(sub) - p
    if (_tr.chunks.length == target.chunks.length - 1 &&
        _sr.chunks.length == source.chunks.length - 1) Some((_sr, _tr))
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

  private def removeSAppChunk(source: SFormula, target: SFormula, tFrame: SApp, sub: Subst) = {
    val _tr = removeSAppIgnoringTag(target, tFrame)
    val _sr = removeSAppIgnoringTag(source.subst(sub), tFrame)
    if (_tr.chunks.length == target.chunks.length - 1 &&
        _sr.chunks.length == source.chunks.length - 1) Some((_sr, _tr))
    else None
  }

  private def frameFromCommonBlock(source: SFormula, target: SFormula,
                                   b: Block, boundVars: Set[Var], sub: Subst): Option[(SFormula, SFormula, SFormula, Subst)] = {
    val sourceSubst = source.subst(sub)
    if (!target.chunks.contains(b) || !sourceSubst.chunks.contains(b)) return None
    // Assuming b.loc is Var, as otherwise the previous method would return None
    val newBoundVars = boundVars + b.loc.asInstanceOf[Var]
    for {
      subHeapT <- findBlockRootedSubHeap(b, target)
      subHeapS <- findBlockRootedSubHeap(b, sourceSubst)
      ugt = UnificationGoal(Assertion(pTrue, subHeapT), Set.empty)
      ugs = UnificationGoal(Assertion(pTrue, subHeapS), Set.empty)
      sub1 <- {
        unify(ugt, ugs, boundInBoth = newBoundVars, needRefreshing = false)
      }
    } yield {
      val _tr = target - subHeapT.chunks
      val _sr = (sourceSubst - subHeapS.chunks).subst(sub1)
      (_sr, _tr, subHeapT, sub1)
    }
  }

  def removeCommonFrame(source: SFormula, target: SFormula, boundVars: Set[Var]): Seq[FrameChoppingResult] = {

    // Strip as much from the two formulas as possible,
    // and unify in the process, delivering the new substitution
    def stripper(sf: Heaplet, tf: Heaplet, sub: Subst): Option[FrameChoppingResult] = tf match {
      case p@PointsTo(_, _, _) =>
        removeSingleChunk(source, target, p, sub).map {
          case (sr, tr) => FrameChoppingResult(sr, SFormula(List(sf)), tr, SFormula(List(tf)), sub)
        }

      case h@SApp(_, _, _) => removeSAppChunk(source, target, h, sub).map {
        case (sr, tr) => FrameChoppingResult(sr, SFormula(List(sf)), tr, SFormula(List(tf)), sub)
      }

      case b@Block(_, _) =>
        frameFromCommonBlock(source, target, b, boundVars, sub).flatMap {
          case (sr, tr, tfsub, _sub) =>
            assert(sf.isInstanceOf[Block], s"Matching source-frame should be block: ${sf.pp}")
            val sourceSegment = findBlockRootedSubHeap(sf.asInstanceOf[Block], source)
            sourceSegment.map(sfsub => FrameChoppingResult(sr, sfsub, tr, tfsub, sub ++ _sub))
        }
    }

    for {
      s <- chunksForUnifying(source)
      t <- chunksForUnifying(target)
      sub <- tryUnify(t, s, boundVars, false)
      fcr <- stripper(s, t, sub)
    } yield {
      fcr
    }
  }

}
