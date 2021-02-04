package org.tygus.suslik.certification.traversal

import TranslatableOps._
import org.tygus.suslik.certification.traversal.Evaluator.EvaluatorException
import org.tygus.suslik.certification.traversal.Step._
import org.tygus.suslik.logic.Specifications.GoalLabel

import scala.annotation.tailrec

class StackEvaluator[A <: SourceStep[A], B <: DestStep[B]] extends Evaluator[A,B] {
  // A pending evaluation task; tracks which children have and have not been evaluated
  case class Task(value: B, label: GoalLabel, remainingBranches: List[(Tree[A], ContextStack)], resultsSoFar: List[Tree[B]])

  // A stack of pending translation tasks
  type TaskStack = List[Task]

  // A stack of evaluation contexts
  type ContextStack = List[Context[B]]

  def run(tree: Tree[A])(implicit translator: Translator[A,B], printer: TreePrinter[B]): Tree[B] = {
    // Use a child result to fulfill the evaluation task for a parent
    @tailrec
    def backward(taskStack: TaskStack, childResult: Tree[B]): Tree[B] =
      taskStack match {
        case Nil =>
          // no more tasks; return the result
          childResult
        case currTask :: remainingStack =>
          currTask.remainingBranches match {
            case Nil =>
              // received results for all children so topmost task is done; remove from stack and evaluate parent task
              val results = childResult :: currTask.resultsSoFar
              val translatedTree = Tree(currTask.value, currTask.label, results.reverse)
              backward(remainingStack, translatedTree)
            case (nextChild, nextContext) :: remainingBranches =>
              // some siblings remain unvisited; update topmost task with child result and explore next sibling
              val updatedTask = currTask.copy(remainingBranches = remainingBranches, resultsSoFar = childResult :: currTask.resultsSoFar)
              forward(nextChild, nextContext, updatedTask :: remainingStack)
          }
      }

    // Do step-wise translation of current tree under current context, and explore next child
    @tailrec
    def forward(tree: Tree[A], contextStack: ContextStack, taskStack: TaskStack): Tree[B] = {
      // translate tree payload
      val (translatedStep0, childContexts) = tree.step.translate[B]

      // finalize step based on action
      val translatedStep = tree.step.contextAction match {
        case Context.Pop =>
          // process all deferred steps in current context and append to the existing step
          contextStack match {
            case curr :: _ => curr.deferreds.map(k => k(curr.tricks)).foldLeft(translatedStep0){ case (l, r) => l >> r }
            case Nil => throw EvaluatorException(s"step ${tree.step.pp} expects a context pop, but context stack is empty")
          }
        case _ =>
          // don't process deferreds yet
          translatedStep0
      }

      // finalize child contexts based on action
      val childContextStacks = tree.step.contextAction match {
        case Context.Push =>
          // create fresh context
          childContexts.map(_ :: contextStack)
        case Context.Pop =>
          // update caller context
          contextStack match {
            case _ :: next :: rest => childContexts.map(next + _ :: rest)
            case _ :: Nil => childContexts.map(List(_))
            case Nil => throw EvaluatorException(s"cannot pop from empty context stack for step ${tree.step.pp}")
          }
        case Context.Replace =>
          // update current context
          contextStack match {
            case curr :: rest => childContexts.map(curr + _ :: rest)
            case Nil => throw EvaluatorException(s"cannot replace context stack item for step ${tree.step.pp}")
          }
      }

      (tree.children, childContextStacks) match {
        case (Nil, Nil) =>
          // terminal; evaluate the converted node in the context of the current stack
          val result: Tree[B] = Tree(translatedStep, tree.label, Nil)
          backward(taskStack, result)
        case (nextChild :: remainingChildren, nextContext :: remainingContexts) if remainingChildren.length == remainingContexts.length =>
          // non-terminal; create translation task for current tree and visit the first child
          val task = Task(translatedStep, tree.label, remainingChildren.zip(remainingContexts), List.empty)
          forward(nextChild, nextContext, task :: taskStack)
        case _ =>
          throw EvaluatorException(s"expecting ${tree.children.length} children but ${childContextStacks.length} child contexts were generated")
      }
    }

    forward(tree, Nil, Nil)
  }
}
