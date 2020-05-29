package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification.targets.coq.language.Expressions.CVar

package object language {
  type CGamma = Map[CVar, CoqType]
  type CFormals = Seq[(CoqType, CVar)]
  type CPredicateEnv = Map[String, CInductivePredicate]
}
