package org.tygus.suslik.certification.targets.coq.language

import org.tygus.suslik.certification.targets.coq.logic.ProofContextItem

sealed abstract class CoqType extends PrettyPrinting with ProofContextItem

case object CBoolType extends CoqType {
  override def pp: String = "bool"
}

case object CNatType extends CoqType {
  override def pp: String = "nat"
}

case object CPtrType extends CoqType {
  override def pp: String = "ptr"
}

case object CUnitType extends CoqType {
  override def pp: String = "unit"
}

case object CPropType extends CoqType {
  override def pp: String = "Prop"
}

case object CHeapType extends CoqType {
  override def pp: String = "heap"
}

case object CNatSeqType extends CoqType {
  override def pp: String = "seq nat"
}
