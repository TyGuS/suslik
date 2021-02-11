package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.logic.Proof
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}

import scala.annotation.tailrec

object ProofPrinter extends ProofTreePrinter[Proof.Step] {
  override def pp(tree: ProofTree[Proof.Step]): String = {
    case class Item(res: String, todo: List[ProofTree[Proof.Step]])
    @tailrec
    def backward(k: List[Item], res: String): String = k match {
      case Nil => res
      case curr :: rest =>
        curr.todo match {
          case Nil => backward(rest, curr.res ++ res)
          case next :: todo =>
            val item = Item(curr.res ++ res, todo)
            forward(next, item :: rest)
        }
    }
    @tailrec
    def forward(tree: ProofTree[Proof.Step], k: List[Item]): String = {
      val res = tree.step match {
        case s if s.isNoop => ""
        case s:Proof.Then => s"${s.pp};\n"
        case s => s"${s.pp}.\n"
      }
      tree.children match {
        case Nil =>
          backward(k, res)
        case next :: rest =>
          val item = Item(res, rest)
          forward(next, item :: k)
      }
    }
    forward(tree, Nil)
  }
}
