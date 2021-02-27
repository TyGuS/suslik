package org.tygus.suslik.certification.targets.iris.logic

import org.tygus.suslik.certification.targets.iris.heaplang.Types.HType
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{IPredicate, IPureAssertion}
import org.tygus.suslik.certification.translation.CardConstructor
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.language.{Ident, PrettyPrinting}

sealed abstract class IProofStep extends DestStep {}

object IProofStep {

  implicit object ProofTreePrinter extends ProofTreePrinter[IProofStep] {
    override def pp(tree: ProofTree[IProofStep]): String = tree.step match {
      case _ => tree.step.pp ++ "\n" ++ tree.children.map(pp).mkString("\n")
    }
  }

}

case class ICoqName(name: Ident) extends PrettyPrinting {
  override def pp: String = s"${name}"
}

sealed abstract class IIntroPattern extends PrettyPrinting

case class IIdent(name: Ident) extends IIntroPattern {
  override def pp: String = s"${name}"
}

case class IPure(name: Ident) extends IIntroPattern {
  override def pp: String = s"%${name}"
}

case class IIntuitionistic(pattern: IIntroPattern) extends IIntroPattern {
  override def pp: String = s"#${pattern.pp}"
}

case class IPatDestruct(patterns: Seq[IIntroPattern]) extends IIntroPattern {
  override def pp: String = {
    val nonEmptyPats = patterns.filterNot(_.pp.isEmpty)
    val patsStr = s"${nonEmptyPats.map(_.pp).mkString(" & ")}"
    if (nonEmptyPats.length > 1) s"($patsStr)" else patsStr
  }
}

case class IPatList(patterns: Seq[IIntroPattern]) extends IIntroPattern {
  override def pp: String = s"${patterns.map(_.pp).mkString(" ")}"
}

case class IIntros(coq: Seq[ICoqName], iris: IIntroPattern) extends IProofStep {
  override def pp: String = {
    val coqStr = if (coq.nonEmpty) s"(${coq.map(_.pp).mkString(" ")})" else ""
    val irisStr = if (iris.pp.nonEmpty) s""""${iris.pp}"""" else ""
    s"iIntros $coqStr $irisStr."
  }
}

case class IDestruct(hypName: IIdent, coq: Seq[ICoqName], iris: IIntroPattern) extends IProofStep {
  override def pp: String = {
    val coqStr = if (coq.nonEmpty) s"(${coq.map(_.pp).mkString(" ")})" else ""
    val irisStr = if (iris.pp.nonEmpty) s""""${iris.pp}"""" else ""
    s"""iDestruct "${hypName.pp}" as $coqStr $irisStr."""
  }
}

case class ILob(hypName: IIdent, coq: Seq[ICoqName]) extends IProofStep {
  override def pp: String = {
    //    iLöb as "IH" forall (x s _alpha_514 ϕ).
    val coqStr = s"(${coq.map(_.pp).mkString(" ")})"
    s"""iLöb as "${hypName.pp}" forall $coqStr."""
  }

}

case class IOpenCard(pred: IPredicate, constructor: CardConstructor, constrExistentials: Seq[(Ident, HType)]) extends IProofStep {
  override def pp: String = {
    val learn = pred.learnLemmaName(constructor)
    val open = pred.openLemmaName(constructor)
    val tactic = if (constrExistentials.isEmpty) {
      s"""
      |erewrite $learn; try by dispatchPure.
      |rewrite $open.""".stripMargin
    } else {
      s"""
      |edestruct $learn as [${constrExistentials.map(v => v._1).mkString(" ")} ->]; try by dispatchPure.
      |rewrite $open.""".stripMargin
    }
    tactic
  }
}

case class IExists(e: IPureAssertion) extends IProofStep {
  override def pp: String = s"iExists ${e.pp}."
}

case class IRenameSelect(pat: String, into: IIntroPattern) extends IProofStep {
  override def pp: String = s"""iRename select ($pat)%I into "${into.pp}"."""
}

case class IRename(oldName: ICoqName, newName: ICoqName) extends IProofStep {
  override def pp: String = s"try rename ${oldName.pp} into ${newName.pp}."
}

case object IFindApply extends IProofStep {
  override def pp: String = "iFindApply."
}

case object IRewriteHyp extends IProofStep {
  override def pp: String = "iRewriteHyp."
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

case object IBegin extends IProofStep {
  override def pp: String = "ssl_begin."
}

case class IIf(hyp: ICoqName) extends IProofStep {
  override def pp: String = s"ssl_if ${hyp.pp}."
}

case class IDebug(msg: String) extends IProofStep {
  override def pp: String = s"(* $msg *)"
}

case object IFree extends IProofStep {
  override def pp: String = "ssl_free."
}


case object IFinish extends IProofStep {
  override def pp: String = "ssl_finish."
}

case object IEmp extends IProofStep {
  override def pp: String = "try wp_pures."
}

