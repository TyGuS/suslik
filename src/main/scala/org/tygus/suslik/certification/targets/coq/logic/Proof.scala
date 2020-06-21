package org.tygus.suslik.certification.targets.coq.logic

import org.tygus.suslik.certification.targets.coq.language._
import org.tygus.suslik.certification.targets.coq.language.Expressions._

object Proof {
  type ProofScriptProducer = Seq[String] => String

  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: Map[CVar, CoqType],
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String)

  case class UnfoldedSApp(substArgs: Map[CVar, CExpr], substEx: Map[CVar, CExpr], asn: CAssertion)

  case class CEnvironment(spec: CFunSpec,
                          predicates: Seq[CInductivePredicate],
                          usedVars: Set[CVar] = Set.empty,
                          existentials: Map[CVar, CExpr] = Map.empty,
                          callHeapVars: Seq[CVar] = Seq.empty,
                          predUnfoldings: Map[CSApp, UnfoldedSApp] = Map.empty,
                          assumptions: Seq[CAssertion] = Seq.empty
                         ) {
    def copy(spec: CFunSpec = this.spec,
             predicates: Seq[CInductivePredicate] = this.predicates,
             usedVars: Set[CVar] = this.usedVars,
             existentials: Map[CVar, CExpr] = this.existentials,
             callHeapVars: Seq[CVar] = this.callHeapVars,
             predUnfoldings: Map[CSApp, UnfoldedSApp] = this.predUnfoldings,
             assumptions: Seq[CAssertion] = this.assumptions
            ): CEnvironment =
      CEnvironment(spec, predicates, usedVars, existentials, callHeapVars, predUnfoldings, assumptions)

    private var counter = 0
    def generateFreshVar(v: CVar): CVar = {
      val freshVar = CVar(s"${v.name}${counter}")
      counter += 1
      freshVar
    }
  }
}