package org.tygus.suslik.certification.traversal

trait ProofTreePrinter[S <: Step] {
  def pp (tree: ProofTree[S]) : String
}
