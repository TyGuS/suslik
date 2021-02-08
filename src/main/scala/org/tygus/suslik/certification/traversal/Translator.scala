package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

trait Translator[A <: SourceStep, B <: DestStep, C <: ClientContext[B]] {
  def translate(value: A, clientContext: C): Translator.Result[B,C]
}

object Translator {
  case class Result[S <: DestStep, C <: ClientContext[S]](steps: List[S], childrenMeta: List[(Deferreds[S,C], C)])
}