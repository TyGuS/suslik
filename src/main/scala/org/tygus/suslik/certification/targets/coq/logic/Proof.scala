package org.tygus.suslik.certification.targets.coq.logic

import org.tygus.suslik.certification.targets.coq.language._
import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp

object Proof {
  type ProofScriptProducer = Seq[String] => String

  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: Map[CVar, CoqType],
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String)

  case class CEnvironment(spec: CFunSpec,
                          predicates: Seq[CInductivePredicate],
                          ctx: Set[CVar],
                          callHeapVars: Seq[CVar]) {
    def copy(spec: CFunSpec = this.spec,
             predicates: Seq[CInductivePredicate] = this.predicates,
             ctx: Set[CVar] = this.ctx,
             callHeapVars: Seq[CVar] = this.callHeapVars): CEnvironment =
      CEnvironment(spec, predicates, ctx, callHeapVars)

    private var counter = 0
    def generateFreshVar(v: CVar): CVar = {
      val freshVar = CVar(s"${v.name}${counter}")
      counter += 1
      freshVar
    }
  }

  case class CProofStep(app: CRuleApp, next: List[CProofStep])

  case class CProof(root: CProofStep) extends PrettyPrinting {
    override def pp: String = {
      def prependArgsProducer(steps: Seq[String], kont: ProofScriptProducer): ProofScriptProducer =
        steps1 => kont(steps ++ steps1)

      def joinProducer(steps: List[CProofStep], kont: ProofScriptProducer): ProofScriptProducer =
        steps.foldLeft(kont) {
          case (kontAcc, step) =>
            steps1 => traverse(step, prependArgsProducer(steps1, kontAcc))
        }

      def composeProducer(f: ProofScriptProducer, g: ProofScriptProducer): ProofScriptProducer =
        steps => g(Seq(f(steps)))

      @scala.annotation.tailrec
      def traverse(step: CProofStep, kont: ProofScriptProducer): String = {
        val nextKont = composeProducer(step.app.fn, kont)
        step.next match {
          case hd :: tl =>
            traverse(hd, joinProducer(tl, nextKont))
          case Nil =>
            nextKont(Seq.empty)
        }
      }

      val builder = new StringBuilder()
      builder.append("Next Obligation.\n")
      builder.append(traverse(root, _.head))
      builder.append("Qed.\n")
      builder.toString()
    }
  }
}