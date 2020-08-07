package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.language.Types.VSTType
import org.tygus.suslik.certification.targets.vst.language.Expressions.{
CExpr, CSFormula
}
import org.tygus.suslik.certification.targets.vst.language.CFormals
import org.tygus.suslik.language.PrettyPrinting

object Sentences {
  case class CInductivePredicate(
    pred: String, idx: Int, selector: CExpr,
    asn: CAssertion, existentials: Seq[CExpr]) extends PrettyPrinting {

  }

  case class CAssertion(phi: CExpr, sigma: CSFormula) extends PrettyPrinting {

  }

  case class CFunSpec(
    name: String, rType: VSTType,
    params: CFormals, ghostParams: CFormals,
    pre: CAssertion, post: CAssertion) extends PrettyPrinting {
  }

}
