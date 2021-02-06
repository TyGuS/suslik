package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Step._

import scala.collection.immutable.Queue

trait Evaluator[A <: SourceStep, B <: DestStep] {
  def run(node: Tree[A])(implicit translator: Translator[A,B], printer: TreePrinter[B], initialClientContext: ClientContext[B]): Tree[B]
}

object Evaluator {
  case class EvaluatorException(private val message: String) extends Exception(message)

  type ClientContext[S <: DestStep]
  type Deferred[S <: DestStep] = ClientContext[S] => (S, ClientContext[S])
  type Deferreds[S <: DestStep] = Queue[Deferred[S]]

  abstract class EnvAction
  object EnvAction {
    case object PushLayer extends EnvAction
    case object PopLayer extends EnvAction
    case object CurrentLayer extends EnvAction
  }
}