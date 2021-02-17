package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator.DeferredsAction
import org.tygus.suslik.language.PrettyPrinting

trait Step extends PrettyPrinting

object Step {
  trait SourceStep extends Step {
    def deferredsAction: DeferredsAction = DeferredsAction.CurrentLayer
  }
  trait DestStep extends Step
}
