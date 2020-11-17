package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.targets.vst.clang.Expressions.{CExpr, CVar}
import org.tygus.suslik.certification.targets.vst.clang.CTypes.VSTCType


/**
  * package contains encoding of suslik terms in C format */
package object clang {
   /** Typing context - maps variables to types */
  type CGamma = Map[CVar, VSTCType]
  /** Formal parameter specification - types and names of parameters */
  type CFormals = Seq[(VSTCType, CVar)]


}
