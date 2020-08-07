package org.tygus.suslik.certification.targets.vst.program

import org.tygus.suslik.certification.targets.vst.language.Types.VSTType
import org.tygus.suslik.certification.targets.vst.language.Expressions.CVar
import org.tygus.suslik.language.PrettyPrinting

object Statements {

  sealed abstract class CStatement extends PrettyPrinting {
  }

  case class CProcedure(
    name: String, tp: VSTType, formals: Seq[(VSTType, CVar)], body: CStatement) extends
      CStatement {
    }

}
