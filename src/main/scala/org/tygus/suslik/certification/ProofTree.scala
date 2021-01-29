package org.tygus.suslik.certification

import org.tygus.suslik.language.PrettyPrinting

/**
  * Represents an abstract encoding of a proof tree
  *
  * @param rule individual rule
  * @param children list of child nodes
  */
sealed case class ProofTree[T](rule: T, children: List[ProofTree[T]])
                              (implicit printer: ProofTreePrinter[T])
  extends PrettyPrinting {
  override def pp : String = printer.pp(this)
}

trait ProofTreePrinter[T] {
  def pp (tree: ProofTree[T]) : String
}
