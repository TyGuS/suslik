package org.tygus.suslik.certification.targets.iris.heaplang

import org.tygus.suslik.language.PrettyPrinting

object Types {

  sealed abstract class HType extends PrettyPrinting

  case class HIntType() extends HType {
    override def pp: String = "int"
  }
  case class HLocType() extends HType {
    override def pp: String = "loc"
  }
}
