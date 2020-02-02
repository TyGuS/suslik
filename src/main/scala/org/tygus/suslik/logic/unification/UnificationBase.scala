package org.tygus.suslik.logic.unification

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.HasExpressions
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.{PureLogicUtils, SepLogicUtils}

/**
  * Base engine for unification, both for spatial and for pure parts
  *
  * @author Ilya Sergey
  */
trait UnificationBase extends SepLogicUtils with PureLogicUtils {

  type UAtom <: HasExpressions[UAtom]

  // match all target chunks (no leftovers) -- true for spatial case
  val precise: Boolean

  def tryUnify(target: UAtom, source: UAtom, nonFreeInSource: Set[Var]): Seq[Subst]

  protected def extractChunks(goal: UnificationGoal): List[UAtom]

  protected def checkShapesMatch(cs1: List[UAtom], cs2: List[UAtom]): Boolean

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
      (tGhosts.intersect(to.vars).isEmpty || sGhosts.contains(from)) &&
        // If "from" is a parameter (in the source), the "to" also should be a parameter (in the target)
        (!sourceParams.contains(from) || to.vars.forall(targetParams.contains))
    }
  }


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

    // Invariant: none of the keys in acc are present in sourceChunks
    def unifyGo(targetChunks: List[UAtom], sourceChunks: List[UAtom], acc: Subst): Seq[Subst] = targetChunks match {
      case Nil =>
        // No more source chunks to unify
        if (sourceChunks.isEmpty) List(acc) else List()
      case _ :: _ if sourceChunks.isEmpty && !precise =>
        List(acc)
      case tc :: tcss =>
        val options = for {
          // Tries to find amongst chunks a heaplet h', which can be unified with the heaplet h.
          candidate <- sourceChunks
          // If successful, returns a substitution and a list of remaining heaplets
          sbst <- tryUnify(tc, candidate, takenVars)
          remainingAtomsAdapted = sourceChunks.filter(_ != candidate).map(_.subst(sbst))
        } yield {
          assertNoOverlap(acc, sbst)
          unifyGo(tcss, remainingAtomsAdapted, acc ++ sbst)
        }
        options.flatten
    }

    // We used to try all permutations of target chunks here, but that was unnecessary (since post-filtering was disabled) and super slow
    unifyGo(targetChunks, sourceChunks, Map.empty) match {
      case newSubst :: _ =>
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
          case (k, v@Var(_)) => target.formula.vars.contains(v)
          case _ => true
        }
        Some(resultSubst)
      // Otherwise, continue
      case Nil => None
    }
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
case class UnificationGoal(formula: Assertion, @deprecated params: Set[Var]) {
  // def ghosts: Set[Var] = formula.vars -- params

  override def toString: String = s"(${params.map(_.pp).mkString(", ")}) ${formula.pp}"
}

