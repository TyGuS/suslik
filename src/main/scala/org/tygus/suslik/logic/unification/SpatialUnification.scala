package org.tygus.suslik.logic.unification

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic._

/**
  * @author Ilya Sergey
  */
object SpatialUnification extends SepLogicUtils with PureLogicUtils {

  type UAtom = Heaplet

  /**
    * Unification of two formulae based on their spatial parts
    *
    * The result is a substitution of variables in the `source` to the variables in the `target`,
    * with the constraint that parameters of the former are not instantiated with the ghosts
    * of the latter (instantiating ghosts with anything is fine).
    *
    * @param globalNames variables that bound in both source and target
    */
  def unify(target: Assertion,
            source: Assertion,
            globalNames: Set[Var] = Set.empty): Option[Subst] = {

    // Make sure that all substitutable variables in source are fresh wrt. target
    val (freshSourceAsn, freshSubst) = source.refresh(target.vars, globalNames)

    val targetChunks = target.sigma.chunks
    val sourceChunks = freshSourceAsn.sigma.chunks
    if (!checkShapesMatch(targetChunks, sourceChunks)) return None

    // Invariant: none of the keys in acc are present in sourceChunks
    def unifyGo(targetChunks: List[UAtom], sourceChunks: List[UAtom], acc: Subst): Seq[Subst] = targetChunks match {
      case Nil =>
        // No more source chunks to unify
        if (sourceChunks.isEmpty) List(acc) else List()
      case tc :: tcss =>
        val options = for {
          // Tries to find amongst chunks a heaplet h', which can be unified with the heaplet h.
          candidate <- sourceChunks
          // If successful, returns a substitution and a list of remaining heaplets
          sbstCandidates = tryUnify(tc, candidate, target.vars ++ globalNames)
          sbst <- sbstCandidates
          remainingAtomsAdapted = sourceChunks.filter(_ != candidate).map(_.subst(sbst))
        } yield {
          assertNoOverlap(acc, sbst)
          unifyGo(tcss, remainingAtomsAdapted, acc ++ sbst)
        }
        options.flatten
    }

    // We used to try all permutations of target chunks here, but that was unnecessary (since post-filtering was disabled) and super slow
    val candidateSubsts = unifyGo(targetChunks, sourceChunks, Map.empty)
    candidateSubsts match {
      case newSubst :: t =>
        // Returns the first good substitution, doesn't try all of them!
        val composition = compose(freshSubst, newSubst)
        /* [Handling spatial-based unification]
          Sometimes, there are parameters of the function spec, that are not present in the spatial part.
          In this case, freshSubst will contain mappings to the variable that is not present in the current
          goal (target). For those variables, for which we don't have a match, we just remove them from the substitution.
          This is sound, as the result is _A_ substitution, which is correct in the case of loops,
          as it refers to the variable in the scope.
         */
        val resultSubst = composition.filter {
          case (k, v@Var(_)) => target.vars.contains(v)
          case _ => true
        }
        Some(resultSubst)
      // Otherwise, continue
      case Nil => None
    }
  }

  /**
    * Tries to unify two heaplets `target` and `source`, assuming `source` has
    * variables that are either free or in `cantBeSubstituted`.
    *
    * If successful, returns a substitution from `source` free variables to `target` variables
    */
  def tryUnify(target: UAtom,
               source: UAtom,
               cantBeSubstituted: Set[Var]): Seq[Subst] = {
    assert(target.vars.forall(cantBeSubstituted.contains), s"Not all variables of ${target.pp} are in $cantBeSubstituted")
    (target, source) match {
      case (PointsTo(x@Var(_), o1, y), PointsTo(a@Var(_), o2, b)) =>
        if (o1 != o2) Nil else {
          assert(cantBeSubstituted.contains(x))
          assert(y.vars.forall(cantBeSubstituted.contains))
          val sbst = for {
            m1 <- genSubst(x, a, cantBeSubstituted)
            _v2 = b.subst(m1)
            m2 <- genSubst(y, _v2, cantBeSubstituted)
          } yield {
            assertNoOverlap(m1, m2)
            m1 ++ m2
          }
          sbst.toList
        }
      case (Block(x1@Var(_), s1), Block(x2@Var(_), s2)) =>
        if (s1 != s2) Nil else {
          assert(cantBeSubstituted.contains(x1))
          genSubst(x1, x2, cantBeSubstituted).toList
        }
      case (SApp(p1, es1, _, tCard), SApp(p2, es2, _, sCard)) =>
        // Only unify predicates with variables as arguments
        // if es2.forall(_.isInstanceOf[Var])

        if (p1 != p2 || es1.size != es2.size) Nil

        else {
          // [Cardinality] : adapting for substituting cardinalities
          val pairs = (tCard, sCard) :: es1.zip(es2).toList
          
          // Collect the mapping from the predicate parameters
          pairs.foldLeft(Some(Map.empty): Option[Subst]) {
            case (opt, (x1, x2)) => opt match {
              case None => None
              case Some(acc) =>
                genSubst(x1, x2, cantBeSubstituted) match {
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

  ///////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////
  //                              Utility methods                                  //
  ///////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////


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
        case SApp(x1, xs1, _, _) =>
          as2.exists { case SApp(x2, xs2, _, _) => x1 == x2 && xs1.size == xs2.size; case _ => false }
        case _ => false
      }
    if (!checkMatchingApps(as1, as2) || !checkMatchingApps(as2, as1)) return false

    true
  }

  /**
    * Check that substitution does not substitutes ghosts for params
    */
  def checkGhostFlow(sbst: Subst,
                     targetAsn: Assertion, targetParams: Set[Var],
                     sourceAsn: Assertion, sourceParams: Set[Var]) = {
    val tGhosts = targetAsn.ghosts(targetParams)
    assert(targetParams.intersect(tGhosts).isEmpty, s"Non empty sets: $targetParams, $tGhosts")
    val sGhosts = sourceAsn.ghosts(sourceParams)
    assert(sourceParams.intersect(sGhosts).isEmpty, s"Non empty sets: $sourceParams, $sGhosts")
    sbst.forall { case (from, to) =>
      // If "to" is a ghost (in the target), the "from" also should be a ghost (in the source)
      val c1 = tGhosts.intersect(to.vars).isEmpty || sGhosts.contains(from)
      // If "from" is a parameter (in the source), the "to" also should be a parameter (in the target)
      val c2 = !sourceParams.contains(from) || to.vars.forall(targetParams.contains)
      c1 && c2
    }
  }

  protected def genSubst(to: Expr, from: Expr, cantBeSubstituted: Set[Var]): Option[Subst] = {
    if (to == from) Some(Map.empty) // Handling constants etc
    else from match {
      case _from@Var(_) if !cantBeSubstituted.contains(_from) => Some(Map(_from -> to))
      case _ => None
    }
  }


}