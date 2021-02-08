package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Step._

import scala.collection.immutable.Queue

trait Evaluator[A <: SourceStep, B <: DestStep, C <: ClientContext[B]] {
  def run(node: ProofTree[A])(implicit translator: Translator[A,B,C], printer: ProofTreePrinter[B], initialClientContext: C): ProofTree[B]
}

object Evaluator {
  case class EvaluatorException(private val message: String) extends Exception(message)

  trait ClientContext[S <: DestStep]
  type Deferred[S <: DestStep, C <: ClientContext[S]] = C => (S, C)
  type Deferreds[S <: DestStep, C <: ClientContext[S]] = Queue[Deferred[S,C]]

  abstract class EnvAction
  object EnvAction {
    case object PushLayer extends EnvAction
    case object PopLayer extends EnvAction
    case object CurrentLayer extends EnvAction
  }
}