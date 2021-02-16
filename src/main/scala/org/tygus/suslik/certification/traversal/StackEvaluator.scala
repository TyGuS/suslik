package org.tygus.suslik.certification.traversal

import TranslatableOps._
import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._
import org.tygus.suslik.logic.Specifications.GoalLabel

import scala.annotation.tailrec

/**
  * A tail-recursive, stack-based tree traversal with an eval/apply loop
  */
class StackEvaluator[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] extends Evaluator[S,D,C] {
  // A pending evaluation task; tracks which children have and have not been evaluated
  case class Task(values: List[D], label: Option[GoalLabel], remainingBranches: List[(ProofTree[S], DeferredsStack[D,C], C)], resultsSoFar: List[ProofTree[D]])

  // A stack of pending evaluation tasks
  type TaskStack = List[Task]

  def run(tree: ProofTree[S])(implicit translator: Translator[S,D,C], initialClientContext: C): ProofTree[D] = {
    // Use a child result to fulfill the evaluation task for a parent
    @tailrec
    def backward(taskStack: TaskStack, childResult: ProofTree[D]): ProofTree[D] =
      taskStack match {
        case Nil =>
          // no more tasks; return the result
          childResult
        case currTask :: remainingStack =>
          currTask.remainingBranches match {
            case Nil =>
              // received results for all children so topmost task is done; remove from stack and evaluate parent task
              val results = childResult :: currTask.resultsSoFar
              val translatedTree = foldStepsIntoTree(currTask.values, results.reverse, currTask.label)
              backward(remainingStack, translatedTree)
            case (nextChild, nextDeferreds, nextTricks) :: remainingBranches =>
              // some siblings remain unvisited; update topmost task with child result and explore next sibling
              val updatedTask = currTask.copy(remainingBranches = remainingBranches, resultsSoFar = childResult :: currTask.resultsSoFar)
              forward(nextChild, nextDeferreds, nextTricks, updatedTask :: remainingStack)
          }
      }

    // Do step-wise translation of current tree node and explore next child
    @tailrec
    def forward(tree: ProofTree[S], deferredsStack: DeferredsStack[D,C], clientContext: C, taskStack: TaskStack): ProofTree[D] = {
      val res = tree.step.translate[D,C](clientContext)
      if (tree.children.length != res.childParams.length) {
        throw EvaluatorException(s"step ${tree.step.pp} has ${tree.children.length} children but translation returned results for ${res.childParams.length} children")
      }

      val action = tree.step.contextAction
      val (newSteps, childClientContexts) = action.handleDeferreds(deferredsStack, clientContext, res.childParams.map(_._2))
      val steps = res.steps ++ newSteps
      val childDeferredsStacks = res.childParams.map { case (newDeferred, _) =>
        action.updateStack(deferredsStack, newDeferred)
      }

      (tree.children, childDeferredsStacks, childClientContexts).zipped.toList match {
        case Nil =>
          // terminal; evaluate the converted node in the context of the current stack
          val result = foldStepsIntoTree(steps, Nil, tree.label)
          backward(taskStack, result)
        case (nextChild, nextDeferredsStack, nextClientCtx) :: remainingBranches =>
          // non-terminal; create evaluation task for current tree and visit the first child
          val task = Task(steps, tree.label, remainingBranches, List.empty)
          forward(nextChild, nextDeferredsStack, nextClientCtx, task :: taskStack)
      }
    }
    // Create a tree from a list of values
    def foldStepsIntoTree(values: List[D], children: List[ProofTree[D]], label: Option[GoalLabel]): ProofTree[D] =
      values.reverse match {
        case last :: rest => rest.foldLeft(ProofTree(last, children, label)){ case (child, v) => ProofTree(v, List(child), label) }
        case Nil => throw EvaluatorException("expected at least one translated value for this task")
      }

    forward(tree, Nil, initialClientContext, Nil)
  }
}
