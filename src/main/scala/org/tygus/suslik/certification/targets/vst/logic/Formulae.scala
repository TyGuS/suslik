package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.Types.{CoqIntValType, CoqPtrValType, VSTType}
import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.language.PrettyPrinting

object Formulae {

  /** abstract type categorizing all spatial formulae  */
  trait VSTHeaplet extends PrettyPrinting


  /** Spatial formulae
    * ===========================================
    **/

  /** spatial formuala indicating points to - i.e loc :-> [elem1; elem2;...]  */
  case class CDataAt(loc: Expressions.ProofCExpr, elems: List[Expressions.ProofCExpr]) extends VSTHeaplet {
    def count = elems.length
      // returns the type of a proof expression
    override def pp: String = s"(data_at Tsh (tarray (Tunion _sslval noattr) ${count.toString}) [${elems.map(_.pp_as_ssl_union_value).mkString("; ")}] ${loc.pp})"
  }

  /** predicate application
    *
    * @param pred predicate name
    * @param args arguments
    * @param card cardinality of call
    * */
  case class CSApp(pred: String, var args: Seq[Expressions.ProofCExpr], card: Expressions.ProofCExpr) extends VSTHeaplet {
    override def pp: String =
      s"(${pred} ${(args ++ List(card)).map(_.pp).mkString(" ")})"
  }


  /** Spatial Formula
    *
    * @param apps applications in the spatial formula
    **/
  case class VSTSFormula(apps: Seq[CSApp], data_at: Seq[CDataAt]) {
    override def productIterator: Iterator[VSTHeaplet] = (apps.iterator ++ data_at.iterator)
  }

}