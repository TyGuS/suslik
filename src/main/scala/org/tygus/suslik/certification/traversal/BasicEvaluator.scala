package org.tygus.suslik.certification.traversal

import TranslatableOps._
import org.tygus.suslik.certification.traversal.Evaluator.{ClientContext, DeferredsStack, EvaluatorException}
import org.tygus.suslik.certification.traversal.Step.{DestStep, SourceStep}

/**
  * A basic tree traversal implementation
  */
abstract class BasicEvaluator[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] extends Evaluator[S,D,C] {
  override def run(tree: ProofTree[S], initialClientContext: C): ProofTree[D] = {
    def visit(tree: ProofTree[S], parentSteps: List[D], deferredsStack: DeferredsStack[D,C], clientContext: C): ProofTree[D] = {
      val res = tree.step.translate[D, C](clientContext)
      if (tree.children.length != res.childParams.length) {
        throw EvaluatorException(s"step ${tree.step.pp} has ${tree.children.length} children but translation returned results for ${res.childParams.length} children")
      }

      val action = tree.step.deferredsAction
      val (newSteps, childClientContexts) = action.handleDeferreds(deferredsStack, clientContext, res.childParams.map(_._3))
      val steps = parentSteps ++ res.steps ++ newSteps
      val childSteps = res.childParams.map(_._1)
      val childDeferredsStacks = res.childParams.map { case (_, newDeferred, _) =>
        action.updateStack(deferredsStack, newDeferred)
      }

      val childResults = tree.children.zip(childSteps).zip(childDeferredsStacks).zip(childClientContexts).map {
        case (((a, b), c), d) => visit(a, b, c, d)
      }
      foldStepsIntoTree(steps, childResults, tree.label)
    }

    visit(tree, Nil, Nil, initialClientContext)
  }
}
