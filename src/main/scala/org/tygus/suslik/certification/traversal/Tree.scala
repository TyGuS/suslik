package org.tygus.suslik.certification.traversal

import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.logic.Specifications.GoalLabel

case class Tree[S <: Step[S]](step: S, label: GoalLabel, children: List[Tree[S]])
                            (implicit printer: TreePrinter[S])
  extends PrettyPrinting {
  override def pp : String = printer.pp(this)
}

trait TreePrinter[S <: Step[S]] {
  def pp (tree: Tree[S]) : String
}
