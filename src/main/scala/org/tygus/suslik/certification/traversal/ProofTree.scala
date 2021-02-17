package org.tygus.suslik.certification.traversal

import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.logic.Specifications.GoalLabel

/**
  * Represents an abstract encoding of a proof tree
  *
  * @param step a proof step (rule application)
  * @param children list of child nodes
  * @param label the label of the Suslik goal to which the rule was applied
  */
sealed case class ProofTree[S <: Step](step: S, children: List[ProofTree[S]], label: Option[GoalLabel] = None) {
  def pp (implicit printer: ProofTreePrinter[S]) : String = printer.pp(this)
}
