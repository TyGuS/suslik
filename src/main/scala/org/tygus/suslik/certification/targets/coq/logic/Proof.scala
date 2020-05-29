package org.tygus.suslik.certification.targets.coq.logic

import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.language.{CAssertion, CFunSpec, CPredicateEnv, CoqType, PrettyPrinting}

trait ProofContextItem

case class CGoal(pre: CAssertion,
                 post: CAssertion,
                 gamma: Map[CVar, CoqType],
                 programVars: Seq[CVar],
                 universalGhosts: Seq[CVar],
                 fname: String)

case class CEnvironment(goal: CGoal,
                        spec: CFunSpec,
                        ctx: ProofContext,
                        predicates: CPredicateEnv,
                        callHeapVars: Seq[CVar],
                        inductive: Boolean) {
  def copy(goal: CGoal = this.goal,
           spec: CFunSpec = this.spec,
           ctx: ProofContext = this.ctx,
           predicates: CPredicateEnv = this.predicates,
           callHeapVars: Seq[CVar] = this.callHeapVars,
           inductive: Boolean = this.inductive): CEnvironment =
    CEnvironment(goal, spec, ctx, predicates, callHeapVars, inductive)

  def apps: Seq[CSApp] =
    (goal.pre.sigma.collect(_.isInstanceOf[CSApp])
      ++ goal.post.sigma.collect(_.isInstanceOf[CSApp])).toSeq
}

case class CProofStep(app: CRuleApp, next: Seq[CProofStep]) {
  val before: Option[String] = app.before
  val op: Option[String] = app.op
  val after: Seq[String] = app.after
}
case class CProof(root: CProofStep) extends PrettyPrinting {
  override def pp: String = {
    val builder = new StringBuilder()
    def build(prev: Option[String], step: CProofStep): Unit = {
      if (prev.isDefined)
        builder.append(s"${prev.get}\n")
      builder.append(step.before.map(s => s"$s\n").getOrElse(""))
      builder.append(step.op.map(s => s"$s\n").getOrElse(""))
      step.next.toList match {
        case _ :: _ :: _ =>
          step.next.zip(step.after).foreach { case(n, after) => build(Some(after), n) }
        case n :: _ =>
          build(step.after.headOption, n)
        case Nil =>
          builder.append(step.after.mkString("\n"))
          builder.append("\n")
      }
    }
    builder.append("Next Obligation.\n")
    build(None, root)
    builder.append("Qed.\n")
    builder.toString()
  }
}
