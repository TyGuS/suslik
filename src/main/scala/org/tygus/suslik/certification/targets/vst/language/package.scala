package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.targets.vst.language.Expressions.{CExpr, CVar}
import org.tygus.suslik.certification.targets.vst.language.Types.VSTType

/**
  * package encodes a wrapper around VST terms */
package object language {
   /** Typing context - maps variables to types */
  type CGamma = Map[CVar, VSTType]
  /** Formal parameter specification - types and names of parameters */
  type CFormals = Seq[(VSTType, CVar)]

  /** type of mapping in context */
  type CtxMapping = (CExpr, VSTType)

}
