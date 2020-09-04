package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.{CFormals, CTypes}
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
    override def pp: String = {
//      s"(data_at Tsh ${elem_typ.pp_as_ctype} ${elem.pp_as_c_value} ${loc.pp})"
      elem_typ match {
        case ProofTypes.CoqParamType(_) => s"(data_at Tsh (tarray ${elem_typ.pp_as_ctype} 1) [${elem.pp_as_ssl_union_value}] ${loc.pp})"
        case ProofTypes.CoqPtrType => s"(data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr ${elem.pp_as_c_value}] ${loc.pp})"
        case ProofTypes.CoqIntType => s"(data_at Tsh (tarray (Tunion _sslval noattr) 1) [inl ${elem.pp_as_c_value}] ${loc.pp})"
        case ProofTypes.CoqCardType(pred_type) => assert(false, "data at pointing to meta variable"); ???
        case CoqListType(_, length) =>
          s"(data_at Tsh (tarray (Tunion _sslval noattr) ${length}) ${elem.pp_as_ssl_union_value} ${loc.pp})"
      }
    }
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
