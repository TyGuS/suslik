package org.tygus.suslik.certification.targets.htt.program

import org.tygus.suslik.certification.targets.htt.Printer
import org.tygus.suslik.certification.targets.htt.program.Statements.{CGuarded, CIf, CStatement, Noop}
import org.tygus.suslik.certification.traversal.ProofTree

object ProgramPrinter extends Printer[CStatement] {

  case class Item(tree: ProofTree[CStatement], pre: String)

  override def initialize(tree: ProofTree[CStatement]): Item = Item(tree, "")

  override def process(item: Item): (List[String] => String, List[Item]) = {
    val pre = item.pre
    val tree = item.tree
    val k = tree.step match {
      case CIf(selectors) => (children: List[String]) => {
        val branches = selectors.zip(children).reverse
        branches.tail.foldLeft(branches.head._2) { case (eb, (c, tb)) => s"${pre}if ${c.pp}\n${pre}then\n$tb\n${pre}else\n$eb" }
      }
      case CGuarded(c) => (children: List[String]) => s"${pre}if ${c.pp}\n${pre}then\n${children.head}\n${pre}else\n${children(1)}"
      case Noop => (children: List[String]) => children.head
      case _ => (children: List[String]) => s"$pre${tree.step.pp}${children.headOption.map("\n" + _).getOrElse("")}"
    }
    val pre1 = tree.step match {
      case _: CIf | _: CGuarded => pre + "  "
      case _ => pre
    }
    (k, tree.children.map(Item(_, pre1)))
  }
}
