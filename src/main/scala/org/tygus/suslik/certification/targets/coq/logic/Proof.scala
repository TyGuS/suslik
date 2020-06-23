package org.tygus.suslik.certification.targets.coq.logic

import org.tygus.suslik.certification.targets.coq.language._
import org.tygus.suslik.certification.targets.coq.language.Expressions._

object Proof {
  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: Map[CVar, CoqType],
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String)

  case class UnfoldedSApp(substArgs: Map[CVar, CExpr], substEx: Map[CVar, CExpr], asn: CAssertion)

  case class CEnvironment(spec: CFunSpec,
                          predicates: Seq[CInductivePredicate],
                          existentials: Map[CVar, CExpr] = Map.empty,
                          predUnfoldings: Map[CSApp, UnfoldedSApp] = Map.empty
                         ) {
    def copy(spec: CFunSpec = this.spec,
             predicates: Seq[CInductivePredicate] = this.predicates,
             existentials: Map[CVar, CExpr] = this.existentials,
             predUnfoldings: Map[CSApp, UnfoldedSApp] = this.predUnfoldings,
            ): CEnvironment =
      CEnvironment(spec, predicates, existentials, predUnfoldings)
  }
}