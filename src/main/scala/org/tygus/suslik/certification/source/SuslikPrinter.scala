package org.tygus.suslik.certification.source

import SuslikProofStep.{Branch, Open}
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter, TreeVisitor}

object SuslikPrinter extends ProofTreePrinter[SuslikProofStep] with TreeVisitor {
  case class Item(tree: ProofTree[SuslikProofStep], pre: String)
  type Result = String

  override def pp(tree: ProofTree[SuslikProofStep]): String = visit(Item(tree, ""))

  override def process(item: Item): (List[String] => String, List[Item]) = {
    val Item(tree, pre) = item
    val k = (children: List[String]) => tree.step match {
      case r:Branch => s"$pre${r.pp}\n${pre}IfTrue:\n${children.head}\n${pre}IfFalse:\n${children(1)}"
      case r:Open => s"$pre${r.pp}\n${r.selectors.zip(children).map { case (sel, child) => s"${pre}if ${sel.pp}:\n$child" } mkString "\n"}"
      case r => s"$pre${r.pp}${children.headOption.map("\n" + _).getOrElse("")}"
    }
    val pre1 = tree.step match {
      case _:Branch | _:Open => pre + "  "
      case _ => pre
    }
    (k, tree.children.map(Item(_, pre1)))
  }
}
