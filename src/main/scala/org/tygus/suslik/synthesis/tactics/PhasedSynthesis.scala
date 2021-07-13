package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.LogicalRules.{FrameUnfolding, FrameUnfoldingFinal}
import org.tygus.suslik.synthesis.rules.Rules.{GeneratesCode, RuleResult, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules.Close
import org.tygus.suslik.synthesis.rules.UnificationRules.HeapUnifyUnfolding
import org.tygus.suslik.synthesis.rules._

import scala.collection.mutable.ArrayBuffer

class PhasedSynthesis(config: SynConfig) extends Tactic {

  def nextRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal

    val index =
      (if (goal.isUnsolvable) math.pow(2,0) else 0)
    + (if (goal.sketch != Hole) math.pow(2,1) else 0)
    + (if (goal.callGoal.nonEmpty) math.pow(2,2) else 0)
    + (if (goal.hasPredicates()) math.pow(2,3) else 0)
    + (if (goal.post.hasBlocks) math.pow(2,4) else 0)
    + (if (goal.hasBlocks) math.pow(2,5) else 0)
    + (if (goal.hasExistentialPointers) math.pow(2,6) else 0)

    val ordersOfAnyPhaseOrSpecBased = goal.env.ordersOfAnyPhaseOrSpecBased
    val orderOfAnyPhaseOrSpecBased = ordersOfAnyPhaseOrSpecBased.apply(index.toInt)

    val unOrderedAnyPhaseOrSpecBased = Vector (
      anyPhaseRules(goal),
      specBasedRules(node)
    )

    val anyPhaseRulesOrSpecBasedRulesNested = {
      if (goal.env.config.evolutionary)
        List(
          unOrderedAnyPhaseOrSpecBased(orderOfAnyPhaseOrSpecBased.apply(0)),
          unOrderedAnyPhaseOrSpecBased(orderOfAnyPhaseOrSpecBased.apply(1))
        ) else List(unOrderedAnyPhaseOrSpecBased:_*)
    }

    val anyPhaseRulesOrSpecBasedRules = anyPhaseRulesOrSpecBasedRulesNested.flatten

    if (goal.isUnsolvable)
      Nil
    else if (goal.sketch != Hole)
    // Until we encounter a hole, symbolically execute the sketch
      anyPhaseRules(goal).filterNot(_.isInstanceOf[GeneratesCode]) ++
        symbolicExecutionRules(goal) ++
        specBasedRules(node).filterNot(_.isInstanceOf[GeneratesCode])
    else if (goal.callGoal.nonEmpty) callAbductionRules(goal)
    else anyPhaseRulesOrSpecBasedRules
  }

  def filterExpansions(allExpansions: Seq[RuleResult]): Seq[RuleResult] = allExpansions

  protected def specBasedRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal

    if (goal.hasPredicates()) {
      // Unfolding phase: get rid of predicates
      val lastUnfoldingRule = node.ruleHistory.dropWhile(anyPhaseRules(goal).contains).headOption
      if (lastUnfoldingRule.contains(HeapUnifyUnfolding) ||
        lastUnfoldingRule.contains(FrameUnfolding) ||
        lastUnfoldingRule.contains(FrameUnfoldingFinal))
        unfoldingNoUnfoldPhaseRules
      else if (lastUnfoldingRule.contains(Close))
      // Once a rule that works on post was used, only use those
        unfoldingPostPhaseRules
      else unfoldingPhaseRules(goal)
    } else if (goal.post.hasBlocks) {
      // Block phase: get rid of blocks
      postBlockPhaseRules
    } else if (goal.hasBlocks) {
      preBlockPhaseRules
    } else if (goal.hasExistentialPointers) {
      // Pointer phase: match all existential pointers
      pointerPhaseRules
    } else {
      // Pure phase: get rid of all the heap
      purePhaseRules(goal)
    }
  }

  protected def anyPhaseRules(goal:Goal): List[SynthesisRule] = {

    val index =
      (if (goal.isUnsolvable) math.pow(2,0) else 0)
    + (if (goal.sketch != Hole) math.pow(2,1) else 0)
    + (if (goal.callGoal.nonEmpty) math.pow(2,2) else 0)
    + (if (goal.hasPredicates()) math.pow(2,3) else 0)
    + (if (goal.post.hasBlocks) math.pow(2,4) else 0)
    + (if (goal.hasBlocks) math.pow(2,5) else 0)
    + (if (goal.hasExistentialPointers) math.pow(2,6) else 0)

    val ordersOfAnyPhaseRules = goal.env.ordersOfAnyPhaseRules
    val orderOfAnyPhaseRules = ordersOfAnyPhaseRules.apply(index.toInt)

    val unorderedAnyPhaseRules = Vector (
      LogicalRules.StarPartial,
      LogicalRules.NilNotLval,
      LogicalRules.Inconsistency,
      FailRules.PostInconsistent,
      LogicalRules.SubstLeft,
      UnificationRules.SubstRight,
      //    LogicalRules.WeakenPre,
      OperationalRules.ReadRule,
      BranchRules.Branch
    )

    if (goal.env.config.evolutionary) {
      List(
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(0)),
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(1)),
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(2)),
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(3)),
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(4)),
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(5)),
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(6)),
        unorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(7))
      )
    } else
      List(unorderedAnyPhaseRules:_*)
  }

  protected def symbolicExecutionRules(goal:Goal): List[SynthesisRule] = {

    val index =
      (if (goal.isUnsolvable) math.pow(2,0) else 0)
    + (if (goal.sketch != Hole) math.pow(2,1) else 0)
    + (if (goal.callGoal.nonEmpty) math.pow(2,2) else 0)
    + (if (goal.hasPredicates()) math.pow(2,3) else 0)
    + (if (goal.post.hasBlocks) math.pow(2,4) else 0)
    + (if (goal.hasBlocks) math.pow(2,5) else 0)
    + (if (goal.hasExistentialPointers) math.pow(2,6) else 0)

    val ordersOfSymbolicExecutionRules = goal.env.ordersOfSymbolicExecutionRules
    val orderOfSymbolicExecutionRules = ordersOfSymbolicExecutionRules.apply(index.toInt)

    val unOrderedSymbolicExecutionRules =
      Vector(
        SymbolicExecutionRules.Open,
        SymbolicExecutionRules.GuidedRead,
        SymbolicExecutionRules.GuidedWrite,
        SymbolicExecutionRules.GuidedAlloc,
        SymbolicExecutionRules.GuidedFree,
        SymbolicExecutionRules.Conditional,
        //    SymbolicExecutionRules.GuidedCall, // TODO: Fix this later with new call rule
      )

    if (goal.env.config.evolutionary) {
      List(
        unOrderedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(0)),
        unOrderedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(1)),
        unOrderedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(2)),
        unOrderedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(3)),
        unOrderedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(4)),
        unOrderedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(5))
      )
    } else
      List(unOrderedSymbolicExecutionRules:_*)
  }

  protected def unfoldingPhaseRules(goal:Goal): List[SynthesisRule] = {

    val index =
      (if (goal.isUnsolvable) math.pow(2,0) else 0)
    + (if (goal.sketch != Hole) math.pow(2,1) else 0)
    + (if (goal.callGoal.nonEmpty) math.pow(2,2) else 0)
    + (if (goal.hasPredicates()) math.pow(2,3) else 0)
    + (if (goal.post.hasBlocks) math.pow(2,4) else 0)
    + (if (goal.hasBlocks) math.pow(2,5) else 0)
    + (if (goal.hasExistentialPointers) math.pow(2,6) else 0)

    val ordersOfUnfoldingPhaseRules = goal.env.ordersOfUnfoldingPhaseRules
    val orderOfUnfoldingPhaseRules = ordersOfUnfoldingPhaseRules.apply(index.toInt)

    val unOrderedUnfoldingPhaseRules =
      List(
        LogicalRules.FrameUnfolding,
        UnificationRules.HeapUnifyUnfolding,
        UnfoldingRules.AbduceCall,
        UnfoldingRules.Open,
        UnfoldingRules.Close,
        //    UnfoldingRules.AbduceCall, // HERE: move AbduceCall here to achieve old behavior
      )

    if (goal.env.config.evolutionary) {
      List(
        unOrderedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(0)),
        unOrderedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(1)),
        unOrderedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(2)),
        unOrderedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(3)),
        unOrderedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(4))
      )
    } else
      List(unOrderedUnfoldingPhaseRules:_*)
  }

  protected def unfoldingPostPhaseRules: List[SynthesisRule] = List(
    LogicalRules.FrameUnfoldingFinal,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.Close,
  )

  protected def unfoldingNoUnfoldPhaseRules: List[SynthesisRule] = List(
    LogicalRules.FrameUnfoldingFinal,
    UnificationRules.HeapUnifyUnfolding,
  )

  protected def callAbductionRules(goal: Goal): List[SynthesisRule] = {
    List(//LogicalRules.SubstLeft,
      UnificationRules.SubstRight,
      FailRules.PostInconsistent,
      FailRules.CheckPost) ++
      (if (goal.post.sigma.apps.nonEmpty)
        List(LogicalRules.FrameUnfoldingFinal,
          UnificationRules.HeapUnifyUnfolding)
      else if (goal.post.sigma.blocks.nonEmpty)
        List(LogicalRules.FrameBlock,
          UnificationRules.HeapUnifyBlock,
//          OperationalRules.AllocRule
        )
      else if (goal.hasExistentialPointers)
        List(LogicalRules.FrameFlat,
//          OperationalRules.WriteRule,
          UnificationRules.HeapUnifyPointer)
      else
        List(UnfoldingRules.CallRule,
          UnificationRules.SubstRight,
          LogicalRules.FrameFlat,
//          OperationalRules.WriteRule,
          UnificationRules.PickArg,
          UnificationRules.PickCard,
          LogicalRules.GhostWrite,
          UnificationRules.HeapUnifyPure,
          LogicalRules.SimplifyConditional,
          OperationalRules.WriteRule,
//          DelegatePureSynthesis.PureSynthesisNonfinal
          UnificationRules.Pick
          ))
  }

  protected def postBlockPhaseRules: List[SynthesisRule] = List(
      (if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost),
      LogicalRules.FrameBlock,
      UnificationRules.HeapUnifyBlock,
      OperationalRules.AllocRule
  )

  protected def preBlockPhaseRules: List[SynthesisRule] = List(
      OperationalRules.FreeRule
  )

  protected def pointerPhaseRules: List[SynthesisRule] = List(
    if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost,
//    LogicalRules.SubstLeft,
//    UnificationRules.SubstRight,
    FailRules.HeapUnreachable,
    LogicalRules.FrameFlat,
    UnificationRules.HeapUnifyPointer,
  )

  protected def purePhaseRules(goal: Goal): List[SynthesisRule] = {

    val unorderedPurePhaseRules =
    Vector(
      if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost,
      LogicalRules.EmpRule,
//      LogicalRules.SubstLeft,
//      UnificationRules.SubstRight,
      FailRules.HeapUnreachable,
      LogicalRules.FrameFlat,
      UnificationRules.PickCard,
      LogicalRules.GhostWrite,
      UnificationRules.HeapUnifyPure,
      LogicalRules.SimplifyConditional,
      OperationalRules.WriteRule,
      if (config.delegatePure) DelegatePureSynthesis.PureSynthesisFinal else UnificationRules.Pick)
//    ++
//    (if (config.branchAbduction) List(UnificationRules.Pick) else List())

    val index = //TODO refactor.
        (if (goal.isUnsolvable) math.pow(2,0) else 0)
      + (if (goal.sketch != Hole) math.pow(2,1) else 0)
      + (if (goal.callGoal.nonEmpty) math.pow(2,2) else 0)
      + (if (goal.hasPredicates()) math.pow(2,3) else 0)
      + (if (goal.post.hasBlocks) math.pow(2,4) else 0)
      + (if (goal.hasBlocks) math.pow(2,5) else 0)
      + (if (goal.hasExistentialPointers) math.pow(2,6) else 0)

    val ordersOfPurePhaseRules = goal.env.ordersOfPurePhaseRules
    val orderOfPurePhaseRules = ordersOfPurePhaseRules.apply(index.toInt)

    if (goal.env.config.evolutionary) {
      List(
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(0)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(1)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(2)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(3)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(4)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(5)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(6)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(7)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(8)),
        unorderedPurePhaseRules(orderOfPurePhaseRules.apply(9))
      )
    } else
      List(unorderedPurePhaseRules:_*)

  }

}
