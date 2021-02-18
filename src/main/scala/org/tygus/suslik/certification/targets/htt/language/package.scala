package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.targets.htt.language.Expressions.CVar
import org.tygus.suslik.certification.targets.htt.language.Types.HTTType

package object language {
  type CGamma = Map[CVar, HTTType]
  type CFormals = Seq[(CVar, HTTType)]
}
