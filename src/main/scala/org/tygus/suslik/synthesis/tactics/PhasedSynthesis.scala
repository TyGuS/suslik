package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.LogicalRules.{FrameUnfolding, FrameUnfoldingFinal}
import org.tygus.suslik.synthesis.rules.OperationalRules.WriteRule
import org.tygus.suslik.synthesis.rules.Rules.{GeneratesCode, RuleResult, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules.{AbduceCall, Close}
import org.tygus.suslik.synthesis.rules.UnificationRules.HeapUnifyUnfolding
import org.tygus.suslik.synthesis.rules._

import scala.collection.mutable.ArrayBuffer

class PhasedSynthesis(config: SynConfig) extends Tactic {

  val is_static = true

  def nextRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal

    // TODO: maybe I should compute "index" separately for anyPhaseRulesOrSpecBasedRules and sketchHole.
    val index = {
      if (false)
        0
      else
        (   (if (goal.post.hasOpBoolEq) math.pow(2,0) else 0) //for SubstRight
          + (if (goal.pre.hasOpBoolEq) math.pow(2,1) else 0) //for SubstLeft
          //+ (if (goal.pre.isForStarPartial) math.pow(2,1) else 0) //for StarPartial
          + (if (goal.hasHeapletPointsGhostInPre) math.pow(2,2) else 0) // for Read
          )
    }

    def anyPhaseRulesOrSpecBasedRules = {

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

      anyPhaseRulesOrSpecBasedRulesNested.flatten

    }

    def sketchHole = {

      val ordersOfSketchHole = goal.env.ordersOfSketchHole
      val orderOfSketchHole = ordersOfSketchHole.apply(index.toInt)

      val unOrderedSketchHole =
        List (
          anyPhaseRules(goal).filterNot(_.isInstanceOf[GeneratesCode]),
          symbolicExecutionRules(goal),
          specBasedRules(node).filterNot(_.isInstanceOf[GeneratesCode])
        )

      val sketchHoleNested = {
        if (goal.env.config.evolutionary)
          List(
            unOrderedSketchHole(orderOfSketchHole.apply(0)),
            unOrderedSketchHole(orderOfSketchHole.apply(1)),
            unOrderedSketchHole(orderOfSketchHole.apply(2))
          ) else List(unOrderedSketchHole:_*)
      }

      sketchHoleNested.flatten

    }

    if (goal.isUnsolvable) Nil
    else if (goal.sketch != Hole) sketchHole // Until we encounter a hole, symbolically execute the sketch
    else if (goal.callGoal.nonEmpty) callAbductionRules(node)
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
        unfoldingNoUnfoldPhaseRules(goal)
      else if (lastUnfoldingRule.contains(Close))
      // Once a rule that works on post was used, only use those
        unfoldingPostPhaseRules(node)
      else unfoldingPhaseRules(node)
    } else if (goal.post.hasBlocks) {
      // Block phase: get rid of blocks
      postBlockPhaseRules(goal)
    } else if (goal.hasBlocks) {
      preBlockPhaseRules
    } else if (goal.hasExistentialPointers) {
      // Pointer phase: match all existential pointers
      pointerPhaseRules(node)
    } else {
      // Pure phase: get rid of all the heap
      purePhaseRules(node)
    }
  }

  protected def anyPhaseRules(goal:Goal): List[SynthesisRule] = {

    val index = {
      if (false)
        0
      else
        (   (if (goal.post.hasOpBoolEq) math.pow(2,0) else 0) //for SubstRight
          + (if (goal.pre.hasOpBoolEq) math.pow(2,1) else 0) //for SubstLeft
          //+ (if (goal.pre.isForStarPartial) math.pow(2,1) else 0) //for StarPartial
          + (if (goal.hasHeapletPointsGhostInPre) math.pow(2,2) else 0) // for Read
          )
    }

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

    val index = {
      if (is_static)
        0
      else
        0
    }

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

  protected def unfoldingPhaseRules(node:OrNode): List[SynthesisRule] = {

    val goal = node.goal
    val index = {
      if (false)
        0
      else {
          (if (node.isAfter(SymbolicExecutionRules.Open)) math.pow(2,0) else 0) // UnfoldingRules.Close
        + (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2, 1) else 0) // for LogicalRules.FrameUnfolding
      }
    }

    val ordersOfUnfoldingPhaseRules = goal.env.ordersOfUnfoldingPhaseRules
    val orderOfUnfoldingPhaseRules = ordersOfUnfoldingPhaseRules.apply(index.toInt)

    val unOrderedUnfoldingPhaseRules =
      Vector(
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

  protected def unfoldingPostPhaseRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal
    val index = {
      if (false)
        0
      else {
        (if (node.isAfter(SymbolicExecutionRules.Open)) math.pow(2,0) else 0) // for UnfoldingRules.Close
      }
    }

    val ordersOfUnfoldingPostPhaseRules = goal.env.ordersOfUnfoldingPostPhaseRules
    val orderOfUnfoldingPostPhaseRules = ordersOfUnfoldingPostPhaseRules.apply(index.toInt)

    val unOrderedUnfoldingPostPhaseRule =
      List(
        LogicalRules.FrameUnfoldingFinal,
        UnificationRules.HeapUnifyUnfolding,
        UnfoldingRules.Close,
      )

    if (goal.env.config.evolutionary) {
      List(
        unOrderedUnfoldingPostPhaseRule(orderOfUnfoldingPostPhaseRules.apply(0)),
        unOrderedUnfoldingPostPhaseRule(orderOfUnfoldingPostPhaseRules.apply(1)),
        unOrderedUnfoldingPostPhaseRule(orderOfUnfoldingPostPhaseRules.apply(2))
      )
    } else
      List(unOrderedUnfoldingPostPhaseRule:_*)

  }

  protected def unfoldingNoUnfoldPhaseRules(goal: Goal): List[SynthesisRule] = {

    val index = {
      if (is_static)
        0
      else
        0
    }

    val ordersOfUnfoldingNoUnfoldPhaseRules = goal.env.ordersOfUnfoldingNoUnfoldPhaseRules
    val orderOfUnfoldingNoUnfoldPhaseRules = ordersOfUnfoldingNoUnfoldPhaseRules.apply(index.toInt)

    val unOrderedUnfoldingNoUnfoldPhaseRules =
      Vector (
        LogicalRules.FrameUnfoldingFinal,
        UnificationRules.HeapUnifyUnfolding
      )

    if (goal.env.config.evolutionary)
      List(
        unOrderedUnfoldingNoUnfoldPhaseRules(orderOfUnfoldingNoUnfoldPhaseRules.apply(0)),
        unOrderedUnfoldingNoUnfoldPhaseRules(orderOfUnfoldingNoUnfoldPhaseRules.apply(1))
      )
    else
      List(unOrderedUnfoldingNoUnfoldPhaseRules:_*)

  }

  protected def callAbductionRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal

    val index1 = {
      if (false)
        0
      else
        (  (if (goal.post.hasOpBoolEq) math.pow(2,0) else 0) //for SubstRight
          + (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2, 1) else 0) // for LogicalRules.FrameUnfoldingFinal
          )
    }

    val index2 = {
      if (false)
        0
      else
        (    (if (goal.post.hasOpBoolEq) math.pow(2, 0) else 0) //for SubstRight
          + (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2, 1) else 0) // for LogicalRules.FrameBlock
          )
    }

    val index3 = {
      if (false)
        0
      else
        (    (if (goal.post.hasOpBoolEq) math.pow(2, 0) else 0) //for SubstRight
           + (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2, 1) else 0) // for LogicalRules.FrameFlat
          )
    }

      val index4 = {
        if (false)
          0
        else
          (   (if (node.isAfter(OperationalRules.ReadRule)) math.pow(2, 0) else 0) // for OperationalRules.WriteRule
            + (if (node.isJustAfter(AbduceCall)) math.pow(2, 1) else 0) // for UnfoldingRules.CallRule
            + (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2, 2) else 0) // for LogicalRules.FrameFlat
            //+ (if (goal.post.hasOpBoolEq) math.pow(2, 3) else 0)) //for SubstRight
            )
      }

    val ordersOfCallAbductionRules1 = goal.env.ordersOfCallAbductionRules1
    val orderOfCallAbductionRules1 = ordersOfCallAbductionRules1.apply(index1.toInt)

    val ordersOfCallAbductionRules2 = goal.env.ordersOfCallAbductionRules2
    val orderOfCallAbductionRules2 = ordersOfCallAbductionRules2.apply(index2.toInt)

    val ordersOfCallAbductionRules3 = goal.env.ordersOfCallAbductionRules3
    val orderOfCallAbductionRules3 = ordersOfCallAbductionRules3.apply(index3.toInt)

    val ordersOfCallAbductionRules4 = goal.env.ordersOfCallAbductionRules4
    val orderOfCallAbductionRules4 = ordersOfCallAbductionRules4.apply(index4.toInt)

    val unOrderedCallAbductionRulesNested1: Vector[SynthesisRule] =
          Vector(
            //LogicalRules.SubstLeft,
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            LogicalRules.FrameUnfoldingFinal,
            UnificationRules.HeapUnifyUnfolding)

    val unOrderedCallAbductionRulesNested2: Vector[SynthesisRule] =
          Vector(
            //LogicalRules.SubstLeft,
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            LogicalRules.FrameBlock,
            UnificationRules.HeapUnifyBlock
            //          OperationalRules.AllocRule
          )

    val unOrderedCallAbductionRulesNested3: Vector[SynthesisRule] =
          Vector(
            //LogicalRules.SubstLeft,
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            LogicalRules.FrameFlat,
            //          OperationalRules.WriteRule,
            UnificationRules.HeapUnifyPointer
          )

    val unOrderedCallAbductionRulesNested4: Vector[SynthesisRule] =
          Vector(
            //LogicalRules.SubstLeft,
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            UnfoldingRules.CallRule,
            //UnificationRules.SubstRight, // This was probably a typo in the original SuSLik.
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
          )

    val defaultOrderedCallAbductionRulesNest =
      List(
        //LogicalRules.SubstLeft,
        List (UnificationRules.SubstRight),
        List (FailRules.PostInconsistent),
        List(FailRules.CheckPost),
        (if (goal.post.sigma.apps.nonEmpty)
          List(
            LogicalRules.FrameUnfoldingFinal,
            UnificationRules.HeapUnifyUnfolding)
        else if (goal.post.sigma.blocks.nonEmpty)
          List(
            LogicalRules.FrameBlock,
            UnificationRules.HeapUnifyBlock,
            //          OperationalRules.AllocRule
          )
        else if (goal.hasExistentialPointers)
          List(
            LogicalRules.FrameFlat,
            //          OperationalRules.WriteRule,
            UnificationRules.HeapUnifyPointer)
        else
          List(
            UnfoldingRules.CallRule,
            // UnificationRules.SubstRight, // This was probably a typo in the original SuSLik.
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
          )
          )
      )

    val orderedCallAbductionRulesNested =
      if (goal.env.config.evolutionary)
        (if (goal.post.sigma.apps.nonEmpty)
          List(
            unOrderedCallAbductionRulesNested1(orderOfCallAbductionRules1.apply(0)),
            unOrderedCallAbductionRulesNested1(orderOfCallAbductionRules1.apply(1)),
            unOrderedCallAbductionRulesNested1(orderOfCallAbductionRules1.apply(2)),
            unOrderedCallAbductionRulesNested1(orderOfCallAbductionRules1.apply(3)),
            unOrderedCallAbductionRulesNested1(orderOfCallAbductionRules1.apply(4))
          )
        else if (goal.post.sigma.blocks.nonEmpty)
          List(
            unOrderedCallAbductionRulesNested2(orderOfCallAbductionRules2.apply(0)),
            unOrderedCallAbductionRulesNested2(orderOfCallAbductionRules2.apply(1)),
            unOrderedCallAbductionRulesNested2(orderOfCallAbductionRules2.apply(2)),
            unOrderedCallAbductionRulesNested2(orderOfCallAbductionRules2.apply(3)),
            unOrderedCallAbductionRulesNested2(orderOfCallAbductionRules2.apply(4))
          )
        else if (goal.hasExistentialPointers)
          List(
            unOrderedCallAbductionRulesNested3(orderOfCallAbductionRules3.apply(0)),
            unOrderedCallAbductionRulesNested3(orderOfCallAbductionRules3.apply(1)),
            unOrderedCallAbductionRulesNested3(orderOfCallAbductionRules3.apply(2)),
            unOrderedCallAbductionRulesNested3(orderOfCallAbductionRules3.apply(3)),
            unOrderedCallAbductionRulesNested3(orderOfCallAbductionRules3.apply(4))
          )
        else
          List(
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(0)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(1)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(2)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(3)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(4)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(5)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(6)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(7)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(8)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(9)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(10)),
            unOrderedCallAbductionRulesNested4(orderOfCallAbductionRules4.apply(11))
          )
          )
      else
        defaultOrderedCallAbductionRulesNest.flatten

    orderedCallAbductionRulesNested
  }

  protected def postBlockPhaseRules(goal: Goal): List[SynthesisRule] = {

    val index = {
      if (is_static)
        0
      else
        0
    }

    val ordersOfPostBlockPhaseRules = goal.env.ordersOfPostBlockPhaseRules
    val orderOfPostBlockPhaseRules = ordersOfPostBlockPhaseRules.apply(index.toInt)

    val unOrdersOfPostBlockPhaseRules =
      Vector(
        (if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost),
        LogicalRules.FrameBlock,
        UnificationRules.HeapUnifyBlock,
        OperationalRules.AllocRule
      )

    if (goal.env.config.evolutionary)
      List(
        unOrdersOfPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(0)),
        unOrdersOfPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(1)),
        unOrdersOfPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(2)),
        unOrdersOfPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(3))
      )
    else List(unOrdersOfPostBlockPhaseRules:_*)
  }

  protected def preBlockPhaseRules: List[SynthesisRule] = List(
    OperationalRules.FreeRule
  )

  protected def pointerPhaseRules(node:OrNode): List[SynthesisRule] = {

    val goal = node.goal
    val index = {
      if (false)
        0
      else
        (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2,0) else 0) // for LogicalRules.FrameFlat
    }

    val ordersOfPointerPhaseRules = goal.env.ordersOfPointerPhaseRules
    val orderOfPointerPhaseRules = ordersOfPointerPhaseRules.apply(index.toInt)

    val unOrderedPointerPhaseRules =
      Vector(
        if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost,
        //    LogicalRules.SubstLeft,
        //    UnificationRules.SubstRight,
        FailRules.HeapUnreachable,
        LogicalRules.FrameFlat,
        UnificationRules.HeapUnifyPointer,
      )

    if (goal.env.config.evolutionary)
      List(
        unOrderedPointerPhaseRules(orderOfPointerPhaseRules.apply(0)),
        unOrderedPointerPhaseRules(orderOfPointerPhaseRules.apply(1)),
        unOrderedPointerPhaseRules(orderOfPointerPhaseRules.apply(2)),
        unOrderedPointerPhaseRules(orderOfPointerPhaseRules.apply(3))
      )
    else List(unOrderedPointerPhaseRules:_*)

  }

  protected def purePhaseRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal

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

    val index = {
      if (false)
        0
      else (
          (if (node.isAfter(OperationalRules.ReadRule)) math.pow(2,0) else 0) // OperationalRules.WriteRule
        + (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2,1) else 0) // for LogicalRules.FrameFlat
        )
    }

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