package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.targets.htt.language.Expressions.CVar

package object language {
  type CGamma = Map[CVar, HTTType]
  type CFormals = Seq[(HTTType, CVar)]
}
