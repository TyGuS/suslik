package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification.targets.coq.language.Expressions.CVar

package object logic {
  type ProofContext = Map[CVar, ProofContextItem]
}
