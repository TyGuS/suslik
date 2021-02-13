package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}

import scala.annotation.tailrec

trait Printer[S <: DestStep] extends ProofTreePrinter[S] {
  type Item

  case class Task(k: List[String] => String, todo: List[Item], done: List[String])

  def initialize(tree: ProofTree[S]): Item

  def process(item: Item): (List[String] => String, List[Item])

  @tailrec
  private def backward(stack: List[Task], res: String): String = stack match {
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
  private def forward(item: Item, stack: List[Task]): String = {
    val (k, items) = process(item)
    items match {
      case Nil =>
        backward(stack, k(Nil))
      case next :: rest =>
        val task = Task(k, rest, Nil)
        forward(next, task :: stack)
    }
  }

  override def pp(tree: ProofTree[S]): String = {
    forward(initialize(tree), Nil)
  }
}
