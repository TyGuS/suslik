package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.language.CTypes.VSTCType
import org.tygus.suslik.certification.targets.vst.language.Expressions.{CExpr, CVar}
import org.tygus.suslik.certification.targets.vst.language.CFormals
import org.tygus.suslik.certification.targets.vst.logic.Proof.VSTPredicate
import org.tygus.suslik.language.Expressions.Expr
import org.tygus.suslik.language.PrettyPrinting

import scala.collection.SortedSet

object Formulae {

  /** abstract type containing all logical formulae */
  sealed trait VSTFormula

  /** abstract type categorizing all spatial formulae  */
  sealed trait VSTHeaplet


  /** Spatial formulae
    * ===========================================
    * */

  /** spatial formuala indicating points to - loc + offset :-> value  */
  case class CPointsTo(loc: CExpr, offset: Int = 0, value: CExpr) extends VSTHeaplet {  }

  /** spatial formula indicating block allocation [loc; sz] */
  case class CBlock(loc: CExpr, sz: Int) extends VSTHeaplet {}

  /** predicate application
    *
    * @param pred predicate name
    * @param args arguments
    * @param card cardinality of call
    **/
  case class CSApp(pred: String, var args: Seq[CExpr], card: CExpr) extends VSTHeaplet {}


  /** Spatial Formula
    * @param apps applications in the spatial formula
    * */
  case class CSFormula(apps: Seq[CSApp], ptss: Seq[CPointsTo], blocks: Seq[CBlock]) extends VSTFormula {
    override def productIterator: Iterator[VSTHeaplet] = (apps.iterator ++ ptss.iterator ++ blocks.iterator)
  }

  case class CInductivePredicate(pred: String, idx: Int, selector: CExpr, asn: CAssertion, existentials: Seq[CExpr]) extends PrettyPrinting {
  }

  case class CAssertion(phi: CExpr, sigma: CSFormula) extends PrettyPrinting {
  }

  case class CFunSpec(
                       name: String, rType: VSTCType,
                       params: CFormals, ghostParams: CFormals,
                       pre: CAssertion, post: CAssertion) extends PrettyPrinting {
  }

}
