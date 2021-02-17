package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter, TreeVisitor}

object ProofPrinter extends ProofTreePrinter[Proof.Step] with TreeVisitor {
  type Item = ProofTree[Proof.Step]
  type Result = String

  override def pp(tree: ProofTree[Proof.Step]): String = visit(tree)

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
