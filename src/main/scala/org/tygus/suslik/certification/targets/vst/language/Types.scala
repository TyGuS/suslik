package org.tygus.suslik.certification.targets.vst.language

import org.tygus.suslik.language.PrettyPrinting

object Types {

  sealed abstract class VSTType extends PrettyPrinting

  case object CBoolType extends VSTType {
    override def pp: String = "tbool"
  }

  case object CNatType extends VSTType {
    override def pp: String = "tint"
  }

  case class CPtrType(of:VSTType) extends VSTType {
    override def pp: String = s"(tptr ${of.pp})"
  }

  case object CUnitType extends VSTType {
    override def pp: String = "tvoid"
  }


}
