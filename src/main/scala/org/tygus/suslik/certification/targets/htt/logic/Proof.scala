package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language._
import org.tygus.suslik.certification.targets.htt.language.Expressions._

object Proof {
  private var currCallId = 0
  def freshCallId: String = { currCallId += 1; s"call$currCallId" }

  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: Map[CVar, HTTType],
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String) {
    val existentials: Seq[CVar] = post.valueVars.diff(programVars ++ universalGhosts)
    def subst(sub: Map[CVar, CExpr]): CGoal = CGoal(
      pre.subst(sub),
      post.subst(sub),
      gamma.map { case (v, t) => v.substVar(sub) -> t },
      programVars.map(_.substVar(sub)),
      universalGhosts.map(_.substVar(sub)),
      fname
    )

    def toFunspec: CFunSpec = {
      val params = programVars.map(v => (gamma(v), v))
      val ghosts = universalGhosts.map(v => (gamma(v), v))
      CFunSpec(fname, CUnitType, params, ghosts, pre, post)
    }
  }

  case class CEnvironment(initialGoal: CGoal,
                          predicates: Map[String, CInductivePredicate],
                          ghostSubst: Map[CVar, CVar] = Map.empty,
                          subst: Map[CVar, CExpr] = Map.empty,
                          unfoldings: Map[CSApp, CInductiveClause] = Map.empty) {
    def copy(initialGoal: CGoal = this.initialGoal,
             predicates: Map[String, CInductivePredicate] = this.predicates,
             ghostSubst: Map[CVar, CVar] = this.ghostSubst,
             subst: Map[CVar, CExpr] = this.subst,
             unfoldings: Map[CSApp, CInductiveClause] = this.unfoldings,
            ): CEnvironment =
      CEnvironment(initialGoal, predicates, ghostSubst, subst, unfoldings)
  }
}