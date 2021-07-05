package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.language.PrettyPrinting

/** Encapsulates all types used in proofs - i.e if these types are pretty printed, then they will be valid Coq terms */
object Types {

  /** proof types */
  sealed abstract class VSTType extends PrettyPrinting {
  }

  sealed abstract class VSTCType extends VSTType {
    def pp_as_ctype: String
  }

  case object CoqPtrValType extends VSTCType {
    override def pp: String = "val"
    override def pp_as_ctype : String = "loc"
  }

  /** type of integers (used to represent the values of variables in a C program) */
  case object CoqIntValType extends VSTCType {
    override def pp: String = "val"
    override def pp_as_ctype : String = "int"
  }

  /** type of integers (used to represent the values of variables in a C program) */
  case object CoqZType extends VSTType {
    override def pp: String = "Z"
  }


  case object CoqIntSetType extends VSTType {
    override def pp: String = "(list Z)"
  }

  /** type of natural numbers (used to type metavariables in Coq proofs) */
  case class CoqCardType(pred_type: String) extends VSTType {
    override def pp: String = s"${pred_type}_card"
  }

}
