package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

trait Translator[A <: SourceStep, B <: DestStep] {
  def translate(value: A, clientContext: ClientContext[B]): Translator.Result[B]
}

object Translator {
  case class Result[S <: DestStep](steps: List[S], childrenMeta: List[(Deferreds[S], ClientContext[S])])
}