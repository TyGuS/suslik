package org.tygus.suslik.certification.traversal

import scala.annotation.tailrec

trait TreeVisitor {
  // The result type of the traversal
  type Result

  // A traversal item (include the tree node and any accumulators)
  type Item

  // Generate a continuation to process the current traversal item, and a list of child items
  def process(item: Item): (List[Result] => Result, List[Item])

  // Recursively visit tree branches and produce result
  def visit(item: Item): Result = forward(item, Nil)

  private case class Task(k: List[Result] => Result, todo: List[Item], done: List[Result])

  @tailrec
  private def backward(stack: List[Task], res: Result): Result = stack match {
    case Nil => res
    case curr :: rest =>
      curr.todo match {
        case Nil => backward(rest, curr.k((res :: curr.done).reverse))
        case next :: todo =>
          val task = curr.copy(todo = todo, done = res :: curr.done)
          forward(next, task :: rest)
      }
  }

  @tailrec
  private def forward(item: Item, stack: List[Task]): Result = {
    val (k, items) = process(item)
    items match {
      case Nil =>
        backward(stack, k(Nil))
      case next :: rest =>
        val task = Task(k, rest, Nil)
        forward(next, task :: stack)
    }
  }
}
