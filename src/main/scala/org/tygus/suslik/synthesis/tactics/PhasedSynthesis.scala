package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.LogicalRules.{FrameUnfolding, FrameUnfoldingFinal}
import org.tygus.suslik.synthesis.rules.Rules.{GeneratesCode, RuleResult, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules._
import org.tygus.suslik.synthesis.rules.UnificationRules.HeapUnifyUnfolding
import org.tygus.suslik.synthesis.rules._

class PhasedSynthesis(config: SynConfig) extends Tactic {

  def nextRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (goal.isUnsolvable)
      Nil
    else if (goal.sketch != Hole)
    // Until we encounter a hole, symbolically execute the sketch
      anyPhaseRules.filterNot(_.isInstanceOf[GeneratesCode]) ++
        symbolicExecutionRules ++
        specBasedRules(node).filterNot(_.isInstanceOf[GeneratesCode])
    else if (goal.callGoal.nonEmpty) callAbductionRules(goal)
    else if (!config.phased)
    // Phase distinction is disabled: use all rules
      anyPhaseRules ++ unfoldingPhaseRules ++
        postBlockPhaseRules ++ preBlockPhaseRules ++
        pointerPhaseRules ++ purePhaseRules
    else anyPhaseRules ++ specBasedRules(node)
  }

  def filterExpansions(allExpansions: Seq[RuleResult]): Seq[RuleResult] = allExpansions

  protected def specBasedRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (goal.hasPredicates()) {
      // Unfolding phase: get rid of predicates
      val lastUnfoldingRule = node.ruleHistory.dropWhile(anyPhaseRules.contains).headOption
      if (lastUnfoldingRule.contains(HeapUnifyUnfolding) ||
        lastUnfoldingRule.contains(FrameUnfolding) ||
        lastUnfoldingRule.contains(FrameUnfoldingFinal))
        unfoldingNoUnfoldPhaseRules
      else if (lastUnfoldingRule.contains(Close))
      // Once a rule that works on post was used, only use those
        unfoldingPostPhaseRules
      else unfoldingPhaseRules
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
      purePhaseRules
    }
  }

  protected def anyPhaseRules: List[SynthesisRule] = List(
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    FailRules.PostInconsistent,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.WeakenPre,
    OperationalRules.ReadRule
  )

  protected def symbolicExecutionRules: List[SynthesisRule] = List(
    SymbolicExecutionRules.Open,
    SymbolicExecutionRules.GuidedRead,
    SymbolicExecutionRules.GuidedWrite,
    SymbolicExecutionRules.GuidedAlloc,
    SymbolicExecutionRules.GuidedFree,
    SymbolicExecutionRules.Conditional,
//    SymbolicExecutionRules.GuidedCall, // TODO: Fix this later with new call rule
  )

  protected def unfoldingPhaseRules: List[SynthesisRule] = List(
    LogicalRules.FrameUnfolding,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Open,
    UnfoldingRules.Close,
  )

  protected def unfoldingPostPhaseRules: List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else FailRules.CheckPost,
    LogicalRules.FrameUnfolding,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.Close,
  )

  protected def unfoldingNoUnfoldPhaseRules: List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else FailRules.CheckPost,
    LogicalRules.FrameUnfoldingFinal,
    UnificationRules.HeapUnifyUnfolding,
  )

  protected def callAbductionRules(goal: Goal): List[SynthesisRule] = {
    List(LogicalRules.SubstLeft,
      UnificationRules.SubstRight,
      FailRules.PostInconsistent,
      FailRules.CheckPost) ++
      (if (goal.post.sigma.apps.nonEmpty)
        List(LogicalRules.FrameUnfolding,
          UnificationRules.HeapUnifyUnfolding)
      else if (goal.post.sigma.blocks.nonEmpty)
        List(LogicalRules.FrameBlock,
          UnificationRules.HeapUnifyBlock,
          OperationalRules.AllocRule)
      else if (goal.hasExistentialPointers)
        List(LogicalRules.FrameFlat,
          OperationalRules.WriteRule,
          UnificationRules.HeapUnifyPointer)
      else
        List(UnfoldingRules.CallRule,
          UnificationRules.SubstRight,
          LogicalRules.FrameFlat,
          OperationalRules.WriteRule,
          UnificationRules.PickArg,
          UnificationRules.PickCard,
          UnificationRules.HeapUnifyPure,
//          DelegatePureSynthesis.PureSynthesisNonfinal
          UnificationRules.Pick
          ))
  }

  protected def postBlockPhaseRules: List[SynthesisRule] = List(
      (if (config.branchAbduction) FailRules.AbduceBranch else FailRules.CheckPost),
      LogicalRules.FrameBlock,
      UnificationRules.HeapUnifyBlock,
      OperationalRules.AllocRule
  )

  protected def preBlockPhaseRules: List[SynthesisRule] = List(
      OperationalRules.FreeRule
  )

  protected def pointerPhaseRules: List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else FailRules.CheckPost,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    FailRules.HeapUnreachable,
    LogicalRules.FrameFlat,
    UnificationRules.HeapUnifyPointer,
  )

  protected def purePhaseRules: List[SynthesisRule] = {
    List(
      if (config.branchAbduction) FailRules.AbduceBranch else FailRules.CheckPost,
      LogicalRules.EmpRule,
      LogicalRules.SubstLeft,
      UnificationRules.SubstRight,
      FailRules.HeapUnreachable,
      LogicalRules.FrameFlat,
      OperationalRules.WriteRule,
      UnificationRules.PickCard,
      UnificationRules.HeapUnifyPure,
      DelegatePureSynthesis.PureSynthesisFinal) ++
    (if (config.branchAbduction) List(UnificationRules.Pick) else List())
  }

}
