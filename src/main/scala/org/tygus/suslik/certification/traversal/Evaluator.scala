package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator.{ClientContext, EvaluatorException}
import org.tygus.suslik.certification.traversal.Step._
import org.tygus.suslik.logic.Specifications.GoalLabel

import scala.collection.immutable.Queue

trait Evaluator[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] {
  implicit val interpreter: Interpreter[S,D,C]

  def run(node: ProofTree[S], initialClientContext: C): ProofTree[D]

  // Create a straight-line tree from a list of values
  def foldStepsIntoTree(values: List[D], children: List[ProofTree[D]], label: Option[GoalLabel]): ProofTree[D] =
    values.reverse match {
      case last :: rest => rest.foldLeft(ProofTree(last, children, label)){ case (child, v) => ProofTree(v, List(child), label) }
      case Nil =>
        children match {
          case child :: Nil => child  // special case: allow translator to emit no immediate steps if there is exactly one child
          case _ => throw EvaluatorException(s"translator produced no immediate steps: expected 1 child but got ${values.length} instead")
        }
    }
}

object Evaluator {
  case class EvaluatorException(private val message: String) extends Exception(message)

  trait ClientContext[D <: DestStep]
  type Deferred[D <: DestStep, C <: ClientContext[D]] = C => (List[D], C)
  type Deferreds[D <: DestStep, C <: ClientContext[D]] = Queue[Deferred[D,C]]

  // A stack of queued deferreds
  type DeferredsStack[D <: DestStep, C <: ClientContext[D]] = List[Deferreds[D,C]]

  abstract class DeferredsAction {
    /**
      * Either release deferreds in topmost stack layer and update child contexts, or (by default) don't do anything
      */
    def handleDeferreds[D <: DestStep, C <: ClientContext[D]](deferredsStack: DeferredsStack[D,C], currentContext: C, childContexts: List[C]): (List[D], List[C]) = (Nil, childContexts)

    /**
      * Update the deferreds stack with a new deferred item
      */
    def updateStack[D <: DestStep, C <: ClientContext[D]](deferredsStack: DeferredsStack[D,C], newDeferred: Option[Deferred[D, C]]): DeferredsStack[D,C]
  }
  object DeferredsAction {
    case object PushLayer extends DeferredsAction {
      override def updateStack[D <: DestStep, C <: ClientContext[D]](deferredsStack: DeferredsStack[D, C], newDeferred: Option[Deferred[D, C]]): DeferredsStack[D, C] = {
        newDeferred match {
          case None => Queue.empty :: deferredsStack
          case Some(d) => Queue(d) :: deferredsStack
        }
      }
    }

    case object PopLayer extends DeferredsAction {
      override def handleDeferreds[D <: DestStep, C <: ClientContext[D]](deferredsStack: DeferredsStack[D,C], currentContext: C, childContexts: List[C]): (List[D], List[C]) = {
        def release(deferreds: Deferreds[D,C], ctx: C): (List[D], C) = {
          deferreds.foldLeft((List.empty[D], ctx)) { case ((steps, ctx), deferred) =>
            val (newSteps, ctx1) = deferred(ctx)
            val steps1 = newSteps.foldLeft(steps){ case (steps, s) => s :: steps }
            (steps1, ctx1)
          }
        }
        deferredsStack match {
          case ds :: _ =>
            if (childContexts.length > 1) {
              throw EvaluatorException(s"step has ${childContexts.length} children, but pop action expects at most 1 child")
            }
            childContexts.headOption match {
              case Some(ctx) =>
                val (res, ctx1) = release(ds, ctx)
                (res.reverse, List(ctx1))
              case None =>
                val (res, _) = release(ds, currentContext)
                (res.reverse, Nil)
            }
          case Nil => throw EvaluatorException("step expects a pop, but deferreds stack is empty")
        }
      }

      override def updateStack[D <: DestStep, C <: ClientContext[D]](deferredsStack: DeferredsStack[D, C], newDeferred: Option[Deferred[D, C]]): DeferredsStack[D, C] = {
        deferredsStack match {
          case _ :: ds :: rest =>
            newDeferred match {
              case None => ds :: rest
              case Some(d) => ds.enqueue(d) :: deferredsStack
            }
          case _ :: Nil => Nil
          case Nil => throw EvaluatorException("step expects a pop, but deferreds stack is empty")
        }
      }
    }

    case object CurrentLayer extends DeferredsAction {
      override def updateStack[D <: DestStep, C <: ClientContext[D]](deferredsStack: DeferredsStack[D, C], newDeferred: Option[Deferred[D, C]]): DeferredsStack[D, C] = {
        deferredsStack match {
          case ds :: rest =>
            newDeferred match {
              case None => deferredsStack
              case Some(d) => ds.enqueue(d) :: rest
            }
          case Nil => throw EvaluatorException("cannot replace deferreds stack item for step")
        }
      }
    }
  }
}