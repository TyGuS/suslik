package org.tygus.suslik.certification.traversal

import TranslatableOps._
import org.tygus.suslik.certification.traversal.Evaluator.{ClientContext, DeferredsStack, EvaluatorException}
import org.tygus.suslik.certification.traversal.Step.{DestStep, SourceStep}

/**
  * A basic tree traversal implementation
  */
abstract class BasicEvaluator[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] extends Evaluator[S,D,C] {
  override def run(tree: ProofTree[S], initialClientContext: C): ProofTree[D] = {
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
      val childResults = next.map(Function.tupled(visit))
      foldStepsIntoTree(steps, childResults, tree.label)
    }

    visit(tree, Nil, initialClientContext)
  }
}
