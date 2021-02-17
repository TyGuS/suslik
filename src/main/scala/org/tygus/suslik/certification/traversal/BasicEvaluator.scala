package org.tygus.suslik.certification.traversal

import TranslatableOps._
import org.tygus.suslik.certification.traversal.Evaluator.{ClientContext, DeferredsStack, EvaluatorException}
import org.tygus.suslik.certification.traversal.Step.{DestStep, SourceStep}

/**
  * A basic tree traversal implementation
  */
class BasicEvaluator[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] extends Evaluator[S,D,C] {
  override def run(tree: ProofTree[S])(implicit translator: Translator[S, D, C], initialClientContext: C): ProofTree[D] = {
    def visit(tree: ProofTree[S], deferredsStack: DeferredsStack[D,C], clientContext: C): ProofTree[D] = {
      val res = tree.step.translate[D, C](clientContext)
      if (tree.children.length != res.childParams.length) {
        throw EvaluatorException(s"step ${tree.step.pp} has ${tree.children.length} children but translation returned results for ${res.childParams.length} children")
      }

      val action = tree.step.deferredsAction
      val (newSteps, childClientContexts) = action.handleDeferreds(deferredsStack, clientContext, res.childParams.map(_._2))
      val steps = res.steps ++ newSteps
      val childDeferredsStacks = res.childParams.map { case (newDeferred, _) =>
        action.updateStack(deferredsStack, newDeferred)
      }

      val next = (tree.children, childDeferredsStacks, childClientContexts).zipped.toList
      val childResults = next.map { case (child, deferredsStack, ctx) => visit(child, deferredsStack, ctx) }
      steps.reverse match {
        case last :: rest => rest.foldLeft(ProofTree(last, childResults, tree.label)) { case (child, v) => ProofTree(v, List(child), tree.label) }
        case Nil => throw EvaluatorException("expected at least one translated value for this task")
      }
    }
    visit(tree, Nil, initialClientContext)
  }
}
