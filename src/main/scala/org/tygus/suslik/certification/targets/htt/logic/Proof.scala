package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language._
import org.tygus.suslik.certification.targets.htt.language.Expressions._

object Proof {
  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: Map[CVar, CoqType],
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String)

  case class CEnvironment(spec: CFunSpec,
                          predicates: Seq[CInductivePredicate],
                          subst: Map[CVar, CExpr] = Map.empty,
                          heapSubst: Map[CSApp, (CSFormula, CInductiveClause)] = Map.empty,
                         ) {
    def copy(spec: CFunSpec = this.spec,
             predicates: Seq[CInductivePredicate] = this.predicates,
             subst: Map[CVar, CExpr] = this.subst,
             heapSubst: Map[CSApp, (CSFormula, CInductiveClause)] = this.heapSubst
            ): CEnvironment =
      CEnvironment(spec, predicates, subst, heapSubst)
  }
}