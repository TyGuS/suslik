package org.tygus.synsl.logic.unification

import org.tygus.synsl.language.Expressions.{Expr, Var}
import org.tygus.synsl.logic._

/**
  * @author Ilya Sergey
  */
object SpatialUnification extends UnificationBase {

  type UAtom = Heaplet

  val precise: Boolean = true


  def tryUnify(target: UAtom, source: UAtom, nonFreeInSource: Set[Var]): Seq[Subst] =
    tryUnify(target, source, nonFreeInSource, tagsMatter = true)

  /**
    * Tries to unify two heaplets `target` and `source`, assuming `source` has
    * variables that are either free or in `nonFreeInSource`.
    *
    * If successful, returns a substitution from `source`'s fresh variables to `target`'s variables
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
      case (SApp(p1, es1, t1), SApp(p2, es2, t2)) =>
        // Only unify predicates with variables as arguments
        // if es2.forall(_.isInstanceOf[Var])
        if (p1 != p2 || es1.size != es2.size ||
            (t1 != t2 && tagsMatter)) Nil
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

  private def frameFromCommonBlock(ft: SFormula, fs: SFormula,
                                   b: Block, boundVars: Set[Var]): Option[(SFormula, SFormula, SFormula, Subst)] = {
    if (!ft.chunks.contains(b) || !fs.chunks.contains(b)) return None
    // Assuming b.loc is Var, as otherwise the previous method would return None
    val newBoundVars = boundVars + b.loc.asInstanceOf[Var]
    for {
      subHeapT <- findBlockRootedSubHeap(b, ft)
      subHeapS <- findBlockRootedSubHeap(b, fs)
      ugt = UnificationGoal(Assertion(PTrue, subHeapT), Set.empty)
      ugs = UnificationGoal(Assertion(PTrue, subHeapS), Set.empty)
      sub <- {
        unify(ugt, ugs, boundInBoth = newBoundVars, needRefreshing = false)
      }
    } yield {
      val _ft = ft - subHeapT.chunks
      val _fs = (fs - subHeapS.chunks).subst(sub)
      (_ft, _fs, subHeapT, sub)
    }
  }


  /**
    * Removes the largest common frame from two spatial formula.
    * Simultaneously unifies the corresponding part in `fs` with `ft`, modulo `boundVars`.
    *
    * The third component of the result is the  common chopped-off sub-formula.
    * The last component is the resulting substitution (from the unification).
    */
  def removeCommonFrame(ft: SFormula, fs: SFormula,
                        boundVars: Set[Var]): Seq[(SFormula, SFormula, SFormula, Subst)] = {

    // Strip as much from the two formulas as possible,
    // and unify in the process, delivering the new substitution
    def stripper(sub: Subst, h: Heaplet) = h match {
      case p@PointsTo(_, _, _) => removeSingleChunk(ft, fs.subst(sub), p).map(x => (x, sub))
      case s@SApp(_, _, _) => removeSAppChunk(ft, fs.subst(sub), s).map(x => (x, sub))
      case b@Block(_, _) => frameFromCommonBlock(ft, fs.subst(sub), b, boundVars).map {
        case (_ft, _fs, f, _sub) => ((_ft, _fs, f), sub ++ _sub)
      }
    }

    for {
      t <- chunksForUnifying(ft)
      s <- chunksForUnifying(fs)
      sub <- tryUnify(t, s, boundVars, false)
      ((_ft, _fs, f), newSub) <- stripper(sub, t)
    } yield {
      (_ft, _fs, f, newSub)
    }
  }

}
