package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

trait Interpreter[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] {
  def interpret(value: S, clientContext: C): Interpreter.Result[D,C]
}

object Interpreter {
  case class Result[D <: DestStep, C <: ClientContext[D]](steps: List[D], childParams: List[(List[D], Option[Deferred[D,C]], C)])
}