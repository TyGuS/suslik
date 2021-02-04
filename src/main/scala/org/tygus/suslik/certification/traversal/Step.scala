package org.tygus.suslik.certification.traversal

import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.logic.Specifications.GoalLabel

trait Step[A <: Step[A]] extends PrettyPrinting

object Step {
  trait SourceStep[A <: SourceStep[A]] extends Step[A] {
    def contextAction: Context.Action = Context.Replace
    def abduceBranch: Option[GoalLabel] = None
  }
  trait DestStep[A <: DestStep[A]] extends Step[A] {
    def >>(that: A): A
  }
}
