package org.tygus.suslik.certification.traversal

import org.tygus.suslik.logic.Specifications.GoalLabel

/**
  * Represents an abstract encoding of a proof tree
  *
  * @param step a proof step (rule application)
  * @param children list of child nodes
  * @param label the label of the Suslik goal to which the rule was applied
  */
case class ProofTree[S <: Step](step: S, children: List[ProofTree[S]], label: Option[GoalLabel] = None)