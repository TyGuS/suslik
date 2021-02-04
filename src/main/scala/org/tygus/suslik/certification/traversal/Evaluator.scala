package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Step._

trait Evaluator[A <: SourceStep[A], B <: DestStep[B]] {
  def run(node: Tree[A])(implicit translator: Translator[A,B], printer: TreePrinter[B]): Tree[B]
}

object Evaluator {
  case class EvaluatorException(private val message: String) extends Exception(message)
}