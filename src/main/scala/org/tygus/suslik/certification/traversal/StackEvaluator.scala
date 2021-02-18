package org.tygus.suslik.certification.traversal

import TranslatableOps._
import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

/**
  * A tail-recursive, stack-based tree traversal with an eval/apply loop
  */
abstract class StackEvaluator[S <: SourceStep, D <: DestStep, C <: ClientContext[D]] extends Evaluator[S,D,C] with TreeVisitor {
  type Result = ProofTree[D]
  type Item = (ProofTree[S], DeferredsStack[D,C], C)

  def run(tree: ProofTree[S], initialClientContext: C): ProofTree[D] = visit((tree, Nil, initialClientContext))

  def process(item: Item): (List[Result] => Result, List[Item]) = {
    val (tree, deferredsStack, clientContext) = item
    val res = tree.step.translate[D,C](clientContext)
    if (tree.children.length != res.childParams.length) {
      throw EvaluatorException(s"step ${tree.step.pp} has ${tree.children.length} children but translation returned results for ${res.childParams.length} children")
    }

    val action = tree.step.deferredsAction
    val (newSteps, childClientContexts) = action.handleDeferreds(deferredsStack, clientContext, res.childParams.map(_._2))
    val steps = res.steps ++ newSteps
    val childDeferredsStacks = res.childParams.map { case (newDeferred, _) =>
      action.updateStack(deferredsStack, newDeferred)
    }

    val k = (results: List[Result]) => foldStepsIntoTree(steps, results, tree.label)
    val next = (tree.children, childDeferredsStacks, childClientContexts).zipped.toList
    (k, next)
  }
}
