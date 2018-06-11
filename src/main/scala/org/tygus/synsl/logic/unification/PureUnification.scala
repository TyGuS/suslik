package org.tygus.synsl.logic.unification

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.logic.PFormula

/**
  * Unification based on pure parts
  *
  * @author Ilya Sergey
  */

object PureUnification extends UnificationBase {
  type UAtom = PFormula

  def tryUnify(target: PFormula, source: PFormula, nonFreeInSource: Set[Var]): Option[Subst] = {
    None
  }

  protected def extractChunks(goal: UnificationGoal): List[PFormula] = conjuncts(goal.formula.phi)

  protected def checkShapesMatch(cs1: List[PFormula], cs2: List[PFormula]): Boolean = {
    // TODO: implement me
    false
  }
}
