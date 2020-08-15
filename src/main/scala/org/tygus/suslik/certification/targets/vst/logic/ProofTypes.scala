package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.language.CTypes.VSTCType
import org.tygus.suslik.certification.targets.vst.language.{CTypes, PrettyPrinting}


/** Encapsulates all types used in proofs - i.e if these types are pretty printed, then they will be valid Coq terms */
object ProofTypes {

  def proof_type_of_c_type(vst: VSTCType) : VSTProofType =
    vst match {
      case CTypes.CIntType => CoqNatType
      case CTypes.CVoidPtrType => CoqPtrType
      case CTypes.CUnitType => ???
    }

  /** proof types */
  sealed abstract class VSTProofType extends PrettyPrinting

  case object CoqPtrType extends VSTProofType {
    override def pp: String = "val"
  }

  case object CoqNatType extends VSTProofType {
    override def pp:String = "Z"
  }

  sealed case class CoqListType(elem: VSTProofType) extends VSTProofType {
    override def pp: String = s"(list ${elem.pp})"
  }

}
