package org.tygus.suslik.certification.traversal

import TranslatableOps._
import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._
import org.tygus.suslik.logic.Specifications.GoalLabel

import scala.annotation.tailrec

class StackEvaluator[A <: SourceStep, B <: DestStep] extends Evaluator[A,B] {
  // A pending evaluation task; tracks which children have and have not been evaluated
  case class Task(values: List[B], label: GoalLabel, remainingBranches: List[(Tree[A], DeferredsStack, ClientContext[B])], resultsSoFar: List[Tree[B]])

  // A stack of pending evaluation tasks
  type TaskStack = List[Task]

  // A stack of queued deferreds
  type DeferredsStack = List[Deferreds[B]]

  def run(tree: Tree[A])(implicit translator: Translator[A,B], printer: TreePrinter[B], initialClientContext: ClientContext[B]): Tree[B] = {
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
              val translatedTree = foldStepsIntoTree(currTask.values, currTask.label, results.reverse)
              backward(remainingStack, translatedTree)
            case (nextChild, nextDeferreds, nextTricks) :: remainingBranches =>
              // some siblings remain unvisited; update topmost task with child result and explore next sibling
              val updatedTask = currTask.copy(remainingBranches = remainingBranches, resultsSoFar = childResult :: currTask.resultsSoFar)
              forward(nextChild, nextDeferreds, nextTricks, updatedTask :: remainingStack)
          }
      }

    // Do step-wise translation of current tree node and explore next child
    @tailrec
    def forward(tree: Tree[A], deferredsStack: DeferredsStack, clientContext: ClientContext[B], taskStack: TaskStack): Tree[B] = {
      val res = tree.step.translate[B](clientContext)
      if (tree.children.length != res.childrenMeta.length) {
        throw EvaluatorException(s"step ${tree.step.pp} has ${tree.children.length} children but translation returned results for ${res.childrenMeta.length} children")
      }
      val (childDeferreds, childClientContexts0) = res.childrenMeta.unzip
      val (steps, childDeferredsStacks, childClientContexts) = tree.step.contextAction match {
        case EnvAction.PopLayer =>
          if (tree.children.length > 1) {
            throw EvaluatorException(s"step ${tree.step.pp} has ${tree.children.length} children, but pop action expects at most 1 child")
          }
          deferredsStack match {
            case deferreds :: remainingDeferreds =>
              // translation should have produced results for 0 or 1 children
              val childDeferreds0 = childDeferreds.headOption.toList
              val childClientContext0 = childClientContexts0.headOption.getOrElse(clientContext)

              // process all deferreds in current stack layer
              val (steps, childClientContext) = deferreds.foldLeft((res.steps.reverse, childClientContext0)) {
                case ((steps, clientCtx), deferred) =>
                  val (step, clientCtx1) = deferred(clientCtx)
                  (step :: steps, clientCtx1)
              }

              // pop current stack layer and enqueue on next stack layer
              val childDeferredsStacks = remainingDeferreds match {
                case nextLayer :: remainingLayers => childDeferreds0.map(newDeferreds => (nextLayer ++ newDeferreds) :: remainingLayers)
                case Nil => childDeferreds0.map(List(_))
              }

              (steps.reverse, childDeferredsStacks, List(childClientContext))
            case Nil => throw EvaluatorException(s"step ${tree.step.pp} expects a pop, but deferreds stack is empty")
          }
        case EnvAction.PushLayer =>
          // create fresh deferreds
          val childDeferredsStacks = childDeferreds.map(_ :: deferredsStack)
          (res.steps, childDeferredsStacks, childClientContexts0)
        case EnvAction.CurrentLayer =>
          deferredsStack match {
            case deferreds :: remainingDeferreds =>
              // enqueue on current deferreds
              val childDeferredsStack = childDeferreds.map(deferreds ++ _ :: remainingDeferreds)
              (res.steps, childDeferredsStack, childClientContexts0)
            case Nil => throw EvaluatorException(s"cannot replace deferreds stack item for step ${tree.step.pp}")
          }
      }

      (tree.children, childDeferredsStacks, childClientContexts).zipped.toList match {
        case Nil =>
          // terminal; evaluate the converted node in the context of the current stack
          val result = foldStepsIntoTree(steps, tree.label, Nil)
          backward(taskStack, result)
        case (nextChild, nextDeferredsStack, nextClientCtx) :: remainingBranches =>
          // non-terminal; create evaluation task for current tree and visit the first child
          val task = Task(steps, tree.label, remainingBranches, List.empty)
          forward(nextChild, nextDeferredsStack, nextClientCtx, task :: taskStack)
      }
    }
    // Create a tree from a list of values
    def foldStepsIntoTree(values: List[B], label: GoalLabel, children: List[Tree[B]]): Tree[B] =
      values.reverse match {
        case last :: rest => rest.foldLeft(Tree(last, label, children)){ case (child, v) => Tree(v, label, List(child)) }
        case Nil => throw EvaluatorException("expected at least one translated value for this task")
      }

    forward(tree, Nil, initialClientContext, Nil)
  }
}
