package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules.{GeneratesCode, RuleResult, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules._
import org.tygus.suslik.synthesis.rules.UnificationRules._
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
    else if (!config.phased)
    // Phase distinction is disabled: use all non top-level rules
      anyPhaseRules ++ unfoldingPhaseRules ++
        postBlockPhaseRules ++ preBlockPhaseRules ++
        pointerPhaseRules ++ purePhaseRules
    else anyPhaseRules ++ specBasedRules(node)
  }

  def filterExpansions(allExpansions: Seq[RuleResult]): Seq[RuleResult] = allExpansions

  protected def specBasedRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (node.parent.map(_.rule).contains(AbduceCall) && node.id.head > 0)
    // TODO: This is a hack: AbduceCall does not make progress,
    // and hence has to be followed by Call, otherwise synthesis gets stuck.
    // Proper fix: merge the two rules
      List(CallRule)
    else if (goal.hasPredicates())
      // Unfolding phase: get rid of predicates
      if (node.parent.map(_.rule).contains(HeapUnifyUnfolding) || node.parent.map(_.rule).contains(Close))
        // Once a rule that works on post was used, only use those
        unfoldingPostPhaseRules
      else unfoldingPhaseRules
    else if (goal.post.hasBlocks)
    // Block phase: get rid of blocks
      postBlockPhaseRules
    else if (goal.hasBlocks)
      preBlockPhaseRules
    else if (goal.hasExistentialPointers)
    // Pointer phase: match all existential pointers
      pointerPhaseRules
    else
    // Pure phase: get rid of all the heap
      purePhaseRules
  }

  protected def anyPhaseRules: List[SynthesisRule] = List(
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    FailRules.PostInconsistent,
    OperationalRules.ReadRule,
    //    LogicalRules.SubstLeft,
  )

  protected def symbolicExecutionRules: List[SynthesisRule] = List(
    SymbolicExecutionRules.Open,
    SymbolicExecutionRules.GuidedRead,
    SymbolicExecutionRules.GuidedWrite,
    SymbolicExecutionRules.GuidedAlloc,
    SymbolicExecutionRules.GuidedFree,
    SymbolicExecutionRules.Conditional,
    SymbolicExecutionRules.GuidedCall,
  )

  protected def unfoldingPhaseRules: List[SynthesisRule] = List(
    LogicalRules.SubstLeftVar,
    //    LogicalRules.SubstRightVar,
    LogicalRules.FrameUnfolding,
    UnfoldingRules.CallRule,
    UnfoldingRules.Open,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Close,
  )

  protected def unfoldingPostPhaseRules: List[SynthesisRule] = List(
    LogicalRules.FrameUnfolding,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.Close,
  )


  protected def postBlockPhaseRules: List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else FailRules.PostInvalid,
    LogicalRules.FrameBlock,
    UnificationRules.HeapUnifyBlock,
    OperationalRules.AllocRule
  )

  protected def preBlockPhaseRules: List[SynthesisRule] = List(
    OperationalRules.FreeRule
  )

  protected def pointerPhaseRules: List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else FailRules.PostInvalid,
    FailRules.HeapUnreachable,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    OperationalRules.WriteRule,
    UnificationRules.HeapUnifyPointer,
  )

  protected def purePhaseRules: List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else FailRules.PostInvalid,
    LogicalRules.EmpRule,
    FailRules.HeapUnreachable,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    OperationalRules.WriteRule,
    //    UnificationRules.PureUnify,
    UnificationRules.HeapUnifyPure,
    UnificationRules.PickCard,
    UnificationRules.Pick,
  )

}
