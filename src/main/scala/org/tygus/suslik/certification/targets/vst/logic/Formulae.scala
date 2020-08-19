package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.CFormals
import org.tygus.suslik.certification.targets.vst.clang.CTypes.VSTCType
import org.tygus.suslik.certification.targets.vst.clang.Expressions.CExpr
import org.tygus.suslik.certification.targets.vst.logic.Proof.Expressions
import org.tygus.suslik.certification.targets.vst.logic.Proof.Expressions.ProofCExpr
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.{CoqIntType, CoqListType, VSTProofType}
import org.tygus.suslik.language.PrettyPrinting

object Formulae {

  /** abstract type categorizing all spatial formulae  */
  sealed trait VSTHeaplet extends PrettyPrinting


  /** Spatial formulae
    * ===========================================
    * */

  /** spatial formuala indicating points to - loc + offset :-> value  */
  case class CDataAt(loc: ProofCExpr, elem_typ: VSTProofType, count: Int, elem: ProofCExpr) extends VSTHeaplet {
    // returns the type of a proof expression
    override def pp: String =
      s"(data_at Tsh ${elem_typ.pp_as_ctype} ${elem.pp_as_c_value} ${loc.pp})"
  }

  /** predicate application
    *
    * @param pred predicate name
    * @param args arguments
    * @param card cardinality of call
    **/
  case class CSApp(pred: String, var args: Seq[ProofCExpr], card: ProofCExpr) extends VSTHeaplet {
    override def pp: String =
      s"(${pred} ${(args ++ List(card)).map(_.pp).mkString(" ")})"
  }


  /** Spatial Formula
    * @param apps applications in the spatial formula
    * */
  case class VSTSFormula(apps: Seq[CSApp], data_at: Seq[CDataAt]) {
    override def productIterator: Iterator[VSTHeaplet] = (apps.iterator ++ data_at.iterator)
 }


}
