package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.htt.Printer
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HExpr, HGuarded, HIf, HNoOp}
import org.tygus.suslik.certification.traversal.ProofTree

object ProgramPrinter extends Printer[HExpr] {

  case class Item(tree: ProofTree[HExpr])

  override def initialize(tree: ProofTree[HExpr]): Item = Item(tree)

  override def process(item: Item): (List[String] => String, List[Item]) = {
    val tree = item.tree
    val k = tree.step match {
      case HIf(selectors) => (children: List[String]) => {
        val branches = selectors.zip(children).reverse
        branches.tail.foldLeft(branches.head._2) { case (eb, (c, tb)) => s"if: ${c.pp}\nthen (\n$tb\n)\nelse (\n$eb\n)" }
      }
      case HGuarded(c) => (children: List[String]) => s"if: ${c.pp}\nthen (\n${children.head}\n)\nelse (\n${children(1)}\n)"
      case HNoOp => (children: List[String]) => children.head
      case _ => (children: List[String]) => s"${tree.step.pp}${children.headOption.map(";; \n" + _).getOrElse("")}"
    }
    (k, tree.children.map(Item))
  }
}
