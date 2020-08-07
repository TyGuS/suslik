package org.tygus.suslik.certification.targets.vst.language

import org.tygus.suslik.language.PrettyPrinting

object Expressions {

  sealed abstract class CExpr extends PrettyPrinting {

  }

  case class CVar(name: String) extends CExpr {
  }

  case class CSApp(pred: String, var args: Seq[CExpr], card: CExpr) extends CExpr {

  }

  case class CSFormula(heapName: String, apps: Seq[CSApp], ptss: Seq[CPointsTo]) extends CExpr {

  }

  case class CPointsTo(loc: CExpr, offset: Int = 0, value: CExpr) extends CExpr {
  }
    
}
