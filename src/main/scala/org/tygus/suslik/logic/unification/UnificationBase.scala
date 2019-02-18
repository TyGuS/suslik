package org.tygus.suslik.logic.unification

import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.Substitutable
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.{PureLogicUtils, SepLogicUtils}

/**
  * Base engine for unification, both for spatial and for pure parts
  *
  * @author Ilya Sergey
  */
trait UnificationBase extends SepLogicUtils with PureLogicUtils {

  type UAtom <: Substitutable[UAtom]

  // match all target chunks (no leftovers) -- true for spatial case
  val precise: Boolean

  def tryUnify(target: UAtom, source: UAtom, nonFreeInSource: Set[Var]): Seq[Subst]

  protected def extractChunks(goal: UnificationGoal): List[UAtom]

  protected def checkShapesMatch(cs1: List[UAtom], cs2: List[UAtom]): Boolean


  /**
    * Unification of two formulae based on their spatial parts
    *
    * The result is a substitution of variables in the `source` to the variables in the `target`,
    * with the constraint that parameters of the former are not instantiated with the ghosts
    * of the latter (instantiating ghosts with anything is fine).
    */
  def unify(target: UnificationGoal, source: UnificationGoal,
            boundInBoth: Set[Var] = Set.empty,
            needRefreshing: Boolean = true): Option[Subst] = {
    // Make sure that all variables in target are fresh wrt. source
    val (freshSource, freshSubst) =
      if (needRefreshing) refreshSource(target, source)
      else (source, {
        val vs = source.formula.vars
        vs.zip(vs).toMap
      })

    val targetChunks = extractChunks(target)
    val sourceChunks = extractChunks(freshSource)
    val takenVars = target.formula.vars ++ boundInBoth

    if (!checkShapesMatch(targetChunks, sourceChunks)) return None

    /**
      * Check that substitution does not substitutes ghosts for params
      */
    def checkSubstWF(sbst: Subst) = {
      val tParams = target.params
      val tGhosts = target.ghosts
      assert(tParams.intersect(tGhosts).isEmpty, s"Non empty sets: $tParams, $tGhosts")
      val sParams = freshSource.params
      val sGhosts = freshSource.ghosts
      assert(sParams.intersect(sGhosts).isEmpty, s"Non empty sets: $sParams, $sGhosts")
      sbst.forall { case (from, to) =>
        // If "to" is a ghost (in the target), the "from" also should be a ghost (in the source)
        (tGhosts.intersect(to.vars).isEmpty || sGhosts.contains(from)) &&
          // If "from" is a parameter (in the source), the "to" also should be a parameter (in the target)
          (!sParams.contains(from) || to.vars.forall(tParams.contains))
      }
    }

    /**
      * Tries to find amongst chunks a heaplet h', which can be unified with the heaplet h.
      * If successful, returns a substitution and a list of remaining heaplets
      */
    def findChunkAndUnify(tc: UAtom, sourceChunks: List[UAtom]): Option[(Subst, List[UAtom])] = {
      val iter = sourceChunks.iterator
      while (iter.hasNext) {
        val candidate = iter.next()
        for {
          sbst <- tryUnify(tc, candidate, takenVars)
          if checkSubstWF(sbst)
        } {
          val remainingAtomsAdapted = sourceChunks.filter(_ != candidate).map(_.subst(sbst))
          return Some(sbst, remainingAtomsAdapted)
        }
      }
      None
    }

    // Invariant: none of the keys in acc are present in sourceChunks
    def unifyGo(targetChunks: List[UAtom], sourceChunks: List[UAtom], acc: Subst): Option[Subst] = targetChunks match {
      case Nil =>
        // No more source chunks to unify
        if (sourceChunks.isEmpty) Some(acc) else None
      case tc :: _ if sourceChunks.isEmpty && !precise =>
        Some(acc)
      case tc :: tcss =>
        findChunkAndUnify(tc, sourceChunks) match {
          case None => None
          // Could not find a matching heaplet
          case Some((sbst, scsUpdated)) =>
            assertNoOverlap(acc, sbst)
            unifyGo(tcss, scsUpdated, acc ++ sbst)
        }
    }

    // Lazily try all permutations of source chunks
    // Ugly imperative stuff below
    val iter = targetChunks.permutations
    while (iter.hasNext) {
      val tChunks = iter.next()
      unifyGo(tChunks, sourceChunks, Map.empty) match {
        case Some(newSubst) =>
          // Returns the first good substitution, doesn't try all of them!
          val newAssertion = source.formula.subst(newSubst)
          val allVarsCaptured = true //newAssertion.vars.forall(target.formula.vars.contains(_))
          // TODO: Once SMT is there, also check implications
          if (allVarsCaptured) {
            val composition = compose(freshSubst, newSubst)
            /* [Handling spatial-based unification]
              Sometimes, there are parameters of the function spec, that are not present in the spatial part.
              In this case, freshSubst will contain mappings to the variable that is not present in the current
              goal (target). For those variables, for which we don't have a match, we just remove them from the substitution.
              This is sound, as the result is _A_ substitution, which is correct in the case of loops,
              as it refers to the variable in the scope.
             */
            val resultSubst = composition.filter {
              case (k, v@Var(_)) => target.formula.vars.contains(v)
              case _ => true
            }
            return Some(resultSubst)
          }
        // Otherwise, continue
        case None =>
      }
    }
    None
  }

  /**
    * Generate fresh names for variables in `source` that occur in `target`
    */
  protected def refreshSource(target: UnificationGoal, source: UnificationGoal): (UnificationGoal, SubstVar) = {
    val (freshSourceFormula, freshSubst) = source.formula.refresh(target.formula.vars)
    val freshParams = source.params.map(_.subst(freshSubst)).asInstanceOf[Set[Var]]
    (UnificationGoal(freshSourceFormula, freshParams), freshSubst)
  }

  protected def genSubst(to: Expr, from: Expr, taken: Set[Var]): Option[Subst] = {
    if (to == from) Some(Map.empty) // Handling constants etc
    else from match {
      case _from@Var(_) if !taken.contains(_from) => Some(Map(_from -> to))
      case _ => None
    }
  }

}

/**
  * A parameterized formula, for which unification produces the substitution
  */
case class UnificationGoal(formula: Assertion, params: Set[Var]) {
  def ghosts: Set[Var] = formula.vars -- params

  override def toString: String = s"(${params.map(_.pp).mkString(", ")}) ${formula.pp}"
}

