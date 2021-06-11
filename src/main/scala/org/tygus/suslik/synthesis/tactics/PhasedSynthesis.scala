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

class PhasedSynthesis(config: SynConfig) extends Tactic {

  def nextRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    val config = goal.env.config
    if (goal.isUnsolvable)
      Nil
    else if (goal.sketch != Hole)
    // Until we encounter a hole, symbolically execute the sketch
      anyPhaseRules(config).filterNot(_.isInstanceOf[GeneratesCode]) ++
        symbolicExecutionRules ++
        specBasedRules(node).filterNot(_.isInstanceOf[GeneratesCode])
    else if (goal.callGoal.nonEmpty) callAbductionRules(goal)
    else anyPhaseRules(config) ++ specBasedRules(node)
  }

  def filterExpansions(allExpansions: Seq[RuleResult]): Seq[RuleResult] = allExpansions

  protected def specBasedRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    val config = goal.env.config
    if (goal.hasPredicates()) {
      // Unfolding phase: get rid of predicates
      val lastUnfoldingRule = node.ruleHistory.dropWhile(anyPhaseRules(config).contains).headOption
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

  //TODO
  private val zippedUnorderedAnyPhaseRules = List(1,1,1,1,1,1,1,1) zip unorderedAnyPhaseRules

  protected def anyPhaseRules(config:SynConfig): List[SynthesisRule] = {
    val generationID  = config.generationID
    val individualID  = config.individualID
    val fileName      = "search_parameters_" + generationID.toString + "_" + individualID.toString + ".json"
    val directoryPath = os.pwd
    val jsonFile      = os.read(directoryPath/"src"/"main"/"scala"/"org"/"tygus"/"suslik"/"synthesis"/"tactics"/"parameters"/fileName)
    val jsonData      = ujson.read(jsonFile)

    val orderOfAnyPhaseRules = jsonData("order_of_any_phase_rules").arr.map(_.num).map(_.toInt)

    if (config.evolutionary)
      List(
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(0)),
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(1)),
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(2)),
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(3)),
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(4)),
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(5)),
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(6)),
        zippedUnorderedAnyPhaseRules(orderOfAnyPhaseRules.apply(7))
      ).filter(p=>{p._1 == 1}).map(_._2)
    else
      List(unorderedAnyPhaseRules:_*)
  }

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
//    UnfoldingRules.AbduceCall, // HERE: move AbduceCall here to achieve old behavior
  )

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
      if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost,
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

  protected def purePhaseRules: List[SynthesisRule] = {
    List(
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
  }

}
