package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HExpr, HGuarded, HIf, HNoOp}
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter, TreeVisitor}

object ProgramPrinter extends ProofTreePrinter[HExpr] with TreeVisitor {

  case class Item(tree: ProofTree[HExpr])
  type Result = String

  override def pp(tree: ProofTree[HExpr]): String = visit(Item(tree))

  override def process(item: Item): (List[String] => String, List[Item]) = {
    val tree = item.tree
    val k = (children: List[String]) => tree.step match {
      case HIf(selectors) =>
        val branches = selectors.zip(children).reverse
        branches.tail.foldLeft(branches.head._2) { case (eb, (c, tb)) => s"if: ${c.pp}\nthen (\n$tb\n)\nelse (\n$eb\n)" }
      case HGuarded(c) => s"if: ${c.pp}\nthen (\n${children.head}\n)\nelse (\n${children(1)}\n)"
      case HNoOp => children.head
      case _ => s"${tree.step.pp}${children.headOption.map(";; \n" + _).getOrElse("")}"
    }
    (k, tree.children.map(Item))
  }
}
