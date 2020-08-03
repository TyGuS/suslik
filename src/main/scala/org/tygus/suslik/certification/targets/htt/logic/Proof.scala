package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.ProofSteps.{ProofStep, nestedDestructL}
import org.tygus.suslik.certification.targets.htt.logic.Sentences._

object Proof {
  private var currCallId = 0
  def freshCallId: String = { currCallId += 1; s"call$currCallId" }

  type Unfoldings = Map[CSApp, CInductiveClause]
  type Subst = Map[CVar, CExpr]
  type SubstVar = Map[CVar, CVar]
  type Gamma = Map[CVar, HTTType]
  type PredicateEnv = Map[String, CInductivePredicate]

  case class Proof(root: ProofStep, params: Seq[CVar]) {
    def pp: String = {
      val obligationTactic = s"Obligation Tactic := intro; move=>${nestedDestructL(params)}; ssl_program_simpl."
      val nextObligation = "Next Obligation."
      val body = root.pp
      val qed = "Qed.\n"
      List(obligationTactic, nextObligation, body, qed).mkString("\n")
    }
  }

  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: Gamma,
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String) {
    val existentials: Seq[CVar] = post.valueVars.diff(programVars ++ universalGhosts)
    def subst(sub: Subst): CGoal = CGoal(
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
                          predicates: PredicateEnv,
                          ghostSubst: SubstVar = Map.empty,
                          subst: Subst = Map.empty,
                          unfoldings: Unfoldings = Map.empty) {
    def copy(initialGoal: CGoal = this.initialGoal,
             predicates: PredicateEnv = this.predicates,
             ghostSubst: SubstVar = this.ghostSubst,
             subst: Subst = this.subst,
             unfoldings: Unfoldings = this.unfoldings,
            ): CEnvironment =
      CEnvironment(initialGoal, predicates, ghostSubst, subst, unfoldings)
  }
}