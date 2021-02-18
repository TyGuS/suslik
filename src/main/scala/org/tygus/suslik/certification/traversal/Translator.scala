package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

trait Translator[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] {
  def translate(value: S, clientContext: C): Translator.Result[D,C]
}

object Translator {
  case class Result[D <: DestStep, C <: ClientContext[D]](steps: List[D], childParams: List[(Option[Deferred[D,C]], C)])
}