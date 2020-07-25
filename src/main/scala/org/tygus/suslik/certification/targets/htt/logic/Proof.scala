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

  case class AppExpansion(constructor: Int, heap: CSFormula, ex: Seq[CExpr])

  case class CEnvironment(spec: CFunSpec,
                          predicates: Seq[CInductivePredicate],
                          ghostSubst: Map[CVar, CVar] = Map.empty,
                          subst: Map[CVar, CExpr] = Map.empty,
                          call: Option[(CGoal, Map[CVar, CVar], Map[CVar, CExpr])] = None,
                          heapSubst: Map[CSApp, AppExpansion] = Map.empty,
                          framedHeaplets: Seq[CExpr] = Seq.empty
                         ) {
    def copy(spec: CFunSpec = this.spec,
             predicates: Seq[CInductivePredicate] = this.predicates,
             ghostSubst: Map[CVar, CVar] = this.ghostSubst,
             subst: Map[CVar, CExpr] = this.subst,
             call: Option[(CGoal, Map[CVar, CVar], Map[CVar, CExpr])] = this.call,
             heapSubst: Map[CSApp, AppExpansion] = this.heapSubst,
             framedHeaplets: Seq[CExpr] = this.framedHeaplets
            ): CEnvironment =
      CEnvironment(spec, predicates, ghostSubst, subst, call, heapSubst)
  }
}