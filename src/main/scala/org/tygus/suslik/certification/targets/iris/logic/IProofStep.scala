package org.tygus.suslik.certification.targets.iris.logic

import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}
import org.tygus.suslik.certification.traversal.Step.DestStep

sealed abstract class IProofStep extends DestStep {}

object IProofStep {

  implicit object ProofTreePrinter extends ProofTreePrinter[IProofStep] {
    override def pp(tree: ProofTree[IProofStep]): String = tree.step match {
      case _ => tree.step.pp ++ "\n" ++ tree.children.map(pp).mkString("\n")
    }
  }

}

case object IInit extends IProofStep {
  override def pp: String = "ssl_begin."
}

case object ILoad extends IProofStep {
  override def pp: String = "ssl_load."
}

case object IStore extends IProofStep {
  override def pp: String = "ssl_store."
}

case object IEmp extends IProofStep {
  override def pp: String = "ssl_finish."
}

