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
    if (coqStr.isEmpty && irisStr.isEmpty) ""
    else s"""iDestruct "${hypName.pp}" as $coqStr $irisStr."""
  }
}

case class ILob(hypName: IIdent, coq: Seq[ICoqName]) extends IProofStep {
  override def pp: String = {
    //    iLöb as "IH" forall (x s _alpha_514 ϕ).
    val coqStr = s"(${coq.map(_.pp).mkString(" ")})"
    s"""iLöb as "${hypName.pp}" forall $coqStr."""
  }

}

case class IUnfold(pred: IPredicate, constructor: CardConstructor) extends IProofStep {
  override def pp: String = {
    val open = pred.openLemmaName(constructor)
    s"ssl_rewrite_first_heap $open."
  }
}

case class IOpenCard(pred: IPredicate,
                     constructor: CardConstructor,
                     constrExistentials: Seq[(Ident, HType)],
                     appHypIdent: IIdent,
                     purePart: IPure,
                    ) extends IProofStep {

  def toDestructPattern(ls: List[String]): String = {
    ls match {
      case Nil => ""
      case ::(x, Nil) => s"[$x]"
      case ::(x, ::(y, Nil)) => s"[$x $y]"
      case ::(x, xs) => s"[$x ${toDestructPattern(xs)}]"
    }

//    (base, ls) match {
//      case (None, :: (vara, :: (varb, rest))) => toDestructPattern(Some(s"[${varb} ${vara}]"))(rest)
//      case (Some(base), ::((vara), rest)) =>
//        toDestructPattern(Some(s"[${vara} ${base}]"))(rest)
//      case (Some(base), Nil) => base
//    }
  }
  override def pp: String = {
    val learn = pred.learnLemmaName(constructor)
    val open = pred.openLemmaName(constructor)
    val tactic = if (constrExistentials.isEmpty) {
      s"""
      |iDestruct ($learn with "${appHypIdent.pp}") as "[${appHypIdent.pp} ${purePart.pp}]".
      |rewrite ${purePart.name}; last by safeDispatchPure.
      |tac_except_post ltac:(rewrite $open).""".stripMargin
    } else {
      // TODO: existentials introduction
      s"""
      |iDestruct ($learn with "${appHypIdent.pp}") as "[${appHypIdent.pp} ${purePart.pp}]".
      |
      |edestruct ${purePart.name} as ${
        toDestructPattern(((constrExistentials.map(v => v._1)).toList ++ List("->")))
      }; first by safeDispatchPure.
      |tac_except_post ltac:(rewrite $open).""".stripMargin
    }
    tactic
  }
}

case object IPullOutExist extends IProofStep {
  override def pp: String = s"pull_out_exist."
}

case class INilNotVal(varName: Ident, hypName: String) extends IProofStep {
  override def pp: String =
    s"""
       |iRename select (${varName} ↦ _)%I into "$hypName".
       |iDestruct (NilNotLval with "$hypName") as "[$hypName %]".
       |""".stripMargin
}

case class IWpApply(applyName: String, exs: Seq[IPureAssertion],
                    pureToInstantiate:Integer,
                    spatialToInstantiate: Integer,
                    applyLemma: Boolean=false) extends IProofStep {
  override def pp: String = {
    val inst = {
      (0 until pureToInstantiate).map(_ => "[]") ++
      (0 until spatialToInstantiate).map(_ => "[$]")
    }.mkString(" ")
    val after = (0 until pureToInstantiate).map(_ => "ssl_finish.").mkString("\n")
    s"""wp_apply ($applyName ${if (applyLemma) "" else "$!"} ${exs.map(e => s"(${e.pp})").mkString(" ")} with "$inst").
       |$after
       |""".stripMargin
  }
}

case class IExistsMany(ex: List[ICoqName]) extends IProofStep {
  override def pp: String = if (ex.isEmpty) "" else s"iExists ${ex.map(_.pp).mkString(", ")}."
}

case class IExists(e: IPureAssertion) extends IProofStep {
  override def pp: String = s"iExists ${e.ppAsPhi}."
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

case class IMalloc(name: ICoqName, sz: Integer) extends IProofStep {
  override def pp: String =
    s"""|wp_alloc ${name.pp} as "?"; try by safeDispatchPure.
       |wp_pures.
       |do $sz try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
       |try rewrite !loc_add_assoc !Z.add_1_r.
       |""".stripMargin
}

case object IFree extends IProofStep {
  override def pp: String = "ssl_free."
}

case object IMovePure extends IProofStep {
  override def pp: String = "movePure."
}

case object IFinish extends IProofStep {
  override def pp: String = "ssl_finish."
}

case object IEmp extends IProofStep {
  override def pp: String = "try wp_pures."
}

