package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.Printer
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}

import scala.annotation.tailrec

object ProofPrinter extends Printer[Proof.Step] {
  type Item = ProofTree[Proof.Step]
  def initialize(tree: ProofTree[Proof.Step]): Item = tree
  def process(item: Item): (List[String] => String, List[Item]) = {
    val k = (children: List[String]) => {
      val res = item.step match {
        case s if s.isNoop => ""
        case s: Proof.Then => s"${s.pp};\n"
        case s => s"${s.pp}.\n"
      }
      s"$res${children.mkString("")}"
    }
    (k, item.children)
  }
}
