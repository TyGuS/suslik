package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator.EnvAction
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.logic.Specifications.GoalLabel

trait Step extends PrettyPrinting

object Step {
  trait SourceStep extends Step {
    def contextAction: EnvAction = EnvAction.CurrentLayer
  }
  trait DestStep extends Step
}
