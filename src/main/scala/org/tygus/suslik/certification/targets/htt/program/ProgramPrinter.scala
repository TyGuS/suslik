package org.tygus.suslik.certification.targets.htt.program

import org.tygus.suslik.certification.targets.htt.program.Statements.{CGuarded, CIf, CStatement, Noop}
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter, TreeVisitor}

object ProgramPrinter extends ProofTreePrinter[CStatement] with TreeVisitor {
  case class Item(tree: ProofTree[CStatement], pre: String)
  type Result = String

  override def pp(tree: ProofTree[CStatement]): String = visit(Item(tree, ""))

  override def process(item: Item): (List[String] => String, List[Item]) = {
    val pre = item.pre
    val tree = item.tree
    val k = (children: List[String]) => tree.step match {
      case CIf(selectors) =>
        val branches = selectors.zip(children).reverse
        branches.tail.foldLeft(branches.head._2) { case (eb, (c, tb)) => s"${pre}if ${c.pp}\n${pre}then\n$tb\n${pre}else\n$eb" }
      case CGuarded(c) => s"${pre}if ${c.pp}\n${pre}then\n${children.head}\n${pre}else\n${children(1)}"
      case Noop => children.head
      case _ => s"$pre${tree.step.pp}${children.headOption.map("\n" + _).getOrElse("")}"
    }
    val pre1 = tree.step match {
      case _: CIf | _: CGuarded => pre + "  "
      case _ => pre
    }
    (k, tree.children.map(Item(_, pre1)))
  }
}
