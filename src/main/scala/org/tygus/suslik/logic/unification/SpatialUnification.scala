package org.tygus.suslik.logic.unification

import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.Substitution
import org.tygus.suslik.logic._

/**
  * @author Ilya Sergey
  */
object SpatialUnification extends UnificationBase {

  type UAtom = Heaplet

  val precise: Boolean = true


  def tryUnify(target: UAtom, source: UAtom, nonFreeInSource: Set[Var]): Seq[Substitution] =
    tryUnify(target, source, nonFreeInSource, tagsMatter = false)

  /**
    * Tries to unify two heaplets `target` and `source`, assuming `source` has
    * variables that are either free or in `nonFreeInSource`.
    *
    * If successful, returns a substitution from `source`'tFrame fresh variables to `target`'tFrame variables
    *
    * @param immTagCompare a way to compar immutability tags when unifying. For example:
    *                      - when unifying pre/post should be strict equality
    *                      - when unifying for a function call, it should be MTag.pre
    */
  def tryUnify(target: UAtom, source: UAtom,
               nonFreeInSource: Set[Var],
               // Take the application level tags into the account
               // should be ignored when used from the *-intro rule
               tagsMatter: Boolean = true,
               //  
               immTagCompare: (MTag, MTag) => Boolean = MTag.pre): Seq[Substitution] = {
    assert(target.vars.forall(nonFreeInSource.contains), s"Not all variables of ${target.pp} are in $nonFreeInSource")

    (target, source) match {
      case (PointsTo(x@Var(_), o1, y, m1), PointsTo(a@Var(_), o2, b, m2)) =>
        if (o1 != o2 ||
          (!immTagCompare(m1, m2) && !MTag.substitutable(m1, m2))
        ) Nil else {
          assert(nonFreeInSource.contains(x))
          assert(y.vars.forall(nonFreeInSource.contains))
          val sbst = for {
            d1 <- genSubst(x, a, nonFreeInSource)
            d2 <- genSubst(y, b.subst(d1), nonFreeInSource)
          } yield {
            assertNoConflict(d1, d2)
            d1 ++ d2
          }
          // if... make substitution for tag here

          if (m1 != m2) {
            val sb = for {
              d1 <- sbst
              d2 <- genSubstMut(m1, m2, nonFreeInSource)
            } yield d1 ++ d2
            sb.toList
          } else {
            sbst.toList
          }
        }
      case (Block(x1@Var(_), s1, m1), Block(x2@Var(_), s2, m2)) =>
        if (s1 != s2 || (!immTagCompare(m1, m2) && !MTag.substitutable(m1, m2))) Nil else {
          assert(nonFreeInSource.contains(x1))
          (genSubst(x1, x2, nonFreeInSource) ++ genSubstMut(m1, m2, nonFreeInSource)).toList
        }
      case (SApp(p1, es1, targetTag, m1, sm1), SApp(p2, es2, sourceTag, m2, sm2)) =>
        // Only unify predicates with variables as arguments
        // if es2.forall(_.isInstanceOf[Var])

        if (p1 != p2 || es1.size != es2.size ||
          !immTagCompare(m1, m2) ||
          !MTag.checkLists(sm1, sm2, immTagCompare) ||
          (targetTag != sourceTag && tagsMatter)) Nil

        else {
          val pairs = es1.zip(es2)

          // Collect the mapping from the predicate parameters
          val sub_param =
            pairs.foldLeft(Some(Substitution()): Option[Substitution]) {
              case (Some(acc), (x1, x2)) =>
                genSubst(x1, x2, nonFreeInSource) match {
                  case Some(sbst) =>
                    assertNoConflict(acc, sbst)
                    Some(acc ++ sbst)
                  case None => None
                }
              case _ => None
            }
          val sub_mut =
            (sm1, sm2) match {
              case (Some(mut1), Some(mut2)) if mut1.length == mut2.length =>
                val mutZip: List[(MTag, MTag)] = mut1.zip(mut2)
                /*
                [Immutability] Computing the mutability tag substitution. 
                The contract here is as follows:
                If a substitution is possible, then the result of the following 
                expression is `Some(mSub)`, where `mSub` maps borrowing annotation names
                to actual mutability annotations. The substitution ignores 
                Mut -> Mut mappings and trivially succeeds for them. The only case when `None`
                is returned is if `genSubstMut(to, from, nonFreeInSource)` fails, e.g.,
                due to unsatisfiable constraint between the already bound names.   
                 */
                mutZip.foldLeft(Some(Substitution.empty): Option[Substitution]) {
                  case (Some(acc), (to, from)) if MTag.pre(to, from) =>
                    genSubstMut(to, from, nonFreeInSource) match {
                      case Some(sbst) =>
                        assertNoConflict(acc, sbst)
                        Some(acc ++ sbst)
                      case None => Some(acc)
                    }
                  case _ => None
                }
              case _ => Some(Substitution.empty)
            }
          val finalSub = for {
            eSub <- sub_param
            mSub <- sub_mut
          } yield eSub ++ mSub
          finalSub.toList
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
    import MTag._

    // Check matching blocks
    val checkMatchingBlocks = (bs1: List[Heaplet], bs2: List[Heaplet]) =>
      bs1.forall {
        case Block(_, s1, m1) => bs2.exists { case Block(_, s2, m2) => s1 == s2 &&
          pre(m1, m2);
        case _ => false
        }
        case _ => false
      }

    if (!checkMatchingBlocks(bs1, bs2) || !checkMatchingBlocks(bs2, bs1)) return false

    // Check matching blocks
    val checkMatchingApps = (as1: List[Heaplet], as2: List[Heaplet]) =>
      as1.forall {
        case SApp(x1, xs1, _, m1, sm1) =>
          as2.exists { case SApp(x2, xs2, _, m2, sm2) => x1 == x2 && xs1.size == xs2.size &&
            pre(m1, m2);
          case _ => false
          }
        case _ => false
      }
    if (!checkMatchingApps(as1, as2) || !checkMatchingApps(as2, as1)) return false

    true
  }


  protected def extractChunks(goal: UnificationGoal): List[UAtom] = goal.formula.sigma.chunks

}
