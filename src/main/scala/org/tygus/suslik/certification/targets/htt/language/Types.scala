package org.tygus.suslik.certification.targets.htt.language

object Types {
  sealed abstract class HTTType extends PrettyPrinting

  case object CBoolType extends HTTType {
    override def pp: String = "bool"
  }

  case object CNatType extends HTTType {
    override def pp: String = "nat"
  }

  case object CPtrType extends HTTType {
    override def pp: String = "ptr"
  }

  case object CUnitType extends HTTType {
    override def pp: String = "unit"
  }

  case object CPropType extends HTTType {
    override def pp: String = "Prop"
  }

  case object CHeapType extends HTTType {
    override def pp: String = "heap"
  }

  case object CNatSeqType extends HTTType {
    override def pp: String = "seq nat"
  }

  case object CCardType extends HTTType {
    override def pp: String = ""
  }
}