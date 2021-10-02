package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.{Heaplet, PointsTo}
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.BranchRules.AbduceBranch
import org.tygus.suslik.synthesis.rules.LogicalRules.{FrameUnfolding, FrameUnfoldingFinal, StarPartial}
import org.tygus.suslik.synthesis.rules.OperationalRules.WriteRule
import org.tygus.suslik.synthesis.rules.Rules.{GeneratesCode, RuleResult, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules.{AbduceCall, Close}
import org.tygus.suslik.synthesis.rules.UnificationRules.HeapUnifyUnfolding
import org.tygus.suslik.synthesis.rules._

import scala.collection.mutable.ArrayBuffer

class PhasedSynthesis(config: SynConfig) extends Tactic {

  val is_static = true

  def preferBranch(node:OrNode): Boolean = node.isJustAfter(AbduceBranch)

  def twoPointersFromSameLocAndOffsetToDiffValue(chunks: List[Heaplet]): Boolean = chunks match {
    case Nil => false
    case fstElement :: tailElements => fstElement match {
      case PointsTo(loc, offset, value) => tailElements.exists(tailElement => tailElement match {
        case PointsTo(loc2, offset2, value2) =>
          (loc.compare(loc2) == 0) && (offset.compare(offset2) == 0) && (value.compare(value2) != 0): Boolean
        case _ => false
      }) || twoPointersFromSameLocAndOffsetToDiffValue(tailElements)
      case _ => twoPointersFromSameLocAndOffsetToDiffValue(tailElements)
    }
  }

  def preferStarPartial(goal:Goal) = {
    val heapsInPre = goal.pre.sigma.chunks
    twoPointersFromSameLocAndOffsetToDiffValue(heapsInPre)
  }

  // just after StarPartial
  def preferInconsistency(node:OrNode): Boolean = node.isJustAfter(StarPartial)

  // has a ghost variable pointed to by a non-ghost in the spacial part of the pre-condition
  def preferReadRule(goal: Goal): Boolean = {
    val heapsInPre = goal.pre.sigma.chunks: List[Heaplet]
    heapsInPre.exists(goal.isHeapletPointsToGhostInPre)
  }

  // equality in the pure part of the post-condition and existential in the pure part of the post-condition
  def preferSubstRight(goal: Goal) = {
    if ((goal.post.phi.conjuncts.exists(_.isOpEq)) || (goal.post.phi.conjuncts.exists(_.isOpBoolEq)))
      (goal.existentials.exists(existential => goal.post.phi.vars.contains(existential)))
    else false
  }

  // equality in the pure part of the pre-condition
  def preferSubstLeft(goal: Goal) = {
    (goal.pre.phi.conjuncts.exists(_.isOpEq)) || (goal.pre.phi.conjuncts.exists(_.isOpBoolEq))
  }

  // both pre- and post-conditions are empty
  def preferEmp(goal: Goal) = goal.pre.sigma.isEmp && goal.post.sigma.isEmp

  // just after a write rule
  def preferFrameAfterWrite(node: OrNode) = {
    (node.isJustAfter(OperationalRules.WriteRule)) || (node.isJustAfter(LogicalRules.GhostWrite))
  }

  // just after Alloc
  def preferWriteAfterAlloc(node: OrNode) = {
    node.isJustAfter(OperationalRules.AllocRule)
  }

  // has an existential in the spacial part of the post-condition
  def preferUnifyHeap(goal: Goal) = {
    val heapsInPost = goal.post.sigma.chunks: List[Heaplet]
    val varsInSpacialPost = heapsInPost.map(_.vars).flatten
    goal.existentials.exists(existential => varsInSpacialPost.contains(existential))
  }

  def preferFrameAfterUnifyHeap(node: OrNode): Boolean = {
    if (node.isJustAfter(UnificationRules.HeapUnifyUnfolding)) true
    else {
      if (node.isJustAfter(UnificationRules.HeapUnifyBlock)) true
      else (node.isJustAfter(UnificationRules.HeapUnifyPointer))
    }
  }

  def preferWriteIfPointers(goal:Goal) = {
    val heapsInPre = goal.pre.sigma.chunks
    val heapsInPost = goal.post.sigma.chunks
    if (heapsInPre.isEmpty || heapsInPost.isEmpty) false
    else heapsInPre.exists(heapInPre => heapsInPost.exists(_.fromSameToDifferent(heapInPre)))
  }


  def preferPickOrHeapUnifyPure(goal: Goal) = {
    val varsInPurePost = goal.post.phi.vars
    goal.existentials.exists(existential => varsInPurePost.contains(existential))
  }

  def preferClose(node: OrNode): Boolean = node.isAfter(UnfoldingRules.Open)

  def preferAnyPhaseRulesStrongly(node: OrNode): Boolean = {
    val goal = node.goal: Goal
    (preferInconsistency(node)) || (preferStarPartial(goal)) || (preferBranch(node))
  }

  def preferSpecBasedRulesStrongly(node:OrNode): Boolean = {
    val goal = node.goal: Goal
    (preferEmp(goal)) || (preferFrameAfterWrite(node)) || (preferWriteAfterAlloc(node))
  }

  def preferAnyPhaseRulesWeakly(node: OrNode): Boolean = {
    val goal = node.goal: Goal
    (preferReadRule(goal) || preferSubstRight(goal) || preferSubstLeft(goal))
  }

  def preferSpecBasedRulesWeakly(node: OrNode): Boolean = {
    val goal = node.goal: Goal
    (preferUnifyHeap(goal)) || (preferFrameAfterUnifyHeap(node)) || (preferWriteIfPointers(goal)) || (preferPickOrHeapUnifyPure(goal))
  }

  def preferCall(node: OrNode): Boolean = node.isJustAfter(UnfoldingRules.AbduceCall)

  def nextRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal

    def anyPhaseRulesOrSpecBasedRules = {

      val index = {
        if (goal.env.runtime_rule_order_selection) {
          if (goal.env.fewer_feature_combinations) {
            if (preferAnyPhaseRulesStrongly(node)) {0} else {
              if (preferSpecBasedRulesStrongly(node)) {1} else {
                if (preferAnyPhaseRulesWeakly(node)) {2} else {
                  if (preferSpecBasedRulesWeakly(node)) {3}
                  else {4}
                }
              }
            }
          }
          else {
            (   (if (preferAnyPhaseRulesStrongly(node)) math.pow(2,0) else 0) //for SubstRight
              + (if (preferSpecBasedRulesStrongly(node)) math.pow(2,1) else 0) //for SubstLeft
              + (if (preferAnyPhaseRulesWeakly(node)) math.pow(2,2) else 0) //for StarPartial
              + (if (preferSpecBasedRulesWeakly(node)) math.pow(2,3) else 0) // for Read
              )
          }
        } else 0
      }

      val ordersOfAnyPhaseOrSpecBased = goal.env.ordersOfAnyPhaseOrSpecBased
      val orderOfAnyPhaseOrSpecBased = ordersOfAnyPhaseOrSpecBased.apply(index.toInt)

      val unOrderedAnyPhaseOrSpecBased = Vector (
        anyPhaseRules(node),
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

      val index = 0
      val ordersOfSketchHole = goal.env.ordersOfSketchHole
      val orderOfSketchHole = ordersOfSketchHole.apply(index.toInt)

      val unOrderedSketchHole =
        List (
          anyPhaseRules(node).filterNot(_.isInstanceOf[GeneratesCode]),
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
      val lastUnfoldingRule = node.ruleHistory.dropWhile(anyPhaseRules(node).contains).headOption
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

  // TODO:
  // - Branch
  // - Inconsistency
  // - StarPartial
  // - Read
  // - SubstRight
  // - SubstLeft
  protected def anyPhaseRules(node:OrNode): List[SynthesisRule] = {

    val goal = node.goal

    val index = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferBranch(node)) {0} else {
            if (preferInconsistency(node) && preferStarPartial(goal)) {1} else {
                if (preferReadRule(goal)) {2} else {
                  if (preferSubstRight(goal) && preferSubstLeft(goal)) {3} else {4}
                }
              }
          }
        }
        else {
            (if (preferBranch(node)) {math.pow(2,0)} else {0})
          + (if (preferInconsistency(node) && preferStarPartial(goal)) {math.pow(2,1)} else {0})
          + (if (preferReadRule(goal)) {math.pow(2,2)} else {0})
          + (if (preferSubstRight(goal) && preferSubstLeft(goal)) {math.pow(2,3)} else {0})
        }
      } else 0
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

    val index = {0}

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
    //TODO: check for a predicate in the post and Open in the past
    val index = { 0
      //if (goal.env.runtime_rule_order_selection) {
      //  if (goal.env.fewer_feature_combinations) {
      //    if (node.isJustAfter(OperationalRules.WriteRule)) {0} else {
      //      if (node.isAfter(SymbolicExecutionRules.Open)) {1} else {2}
      //    }
      //  }
      //  else {
      //    (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2,0) else 0)
      //    + (if (node.isAfter(SymbolicExecutionRules.Open)) math.pow(2, 1) else 0) // for LogicalRules.FrameUnfolding
      //  }
      //} // UnfoldingRules.Close
      //else 0
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
    val index = 0
      //if (goal.env.runtime_rule_order_selection) {
      //  if (goal.env.fewer_feature_combinations) {
      //    if (node.isAfter(SymbolicExecutionRules.Open)) {
      //      0
      //    } else {
      //      1
      //    } // for UnfoldingRules.Close
      //  }
      //  else {
      //    (if (node.isAfter(SymbolicExecutionRules.Open)) {
      //      math.pow(2, 0)
      //    } else {
      //      0
      //    }) // for UnfoldingRules.Close
      //  }
      //}
      //else {0}


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

    val index = {0}

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

  // TODO:
  // Inner4
  // - disjunction of
  //   - call after UnfoldingRules.AbduceCall
  //   - frame because of write
  // - write after Alloc or because of preferWriteIfPointers
  // - pick or HeapUnifyPure because of existential in pure post
  protected def callAbductionRules(node: OrNode): List[SynthesisRule] = {

    val goal = node.goal

    val index1 = 0
      // if (goal.env.runtime_rule_order_selection) {
      //   if (goal.env.fewer_feature_combinations) {
      //     if (node.isJustAfter(OperationalRules.WriteRule)) {0} else {// for LogicalRules.FrameUnfoldingFinal
      //       if (goal.post.hasOpBoolEq) {1} else {2} //for SubstRight
      //     }
      //   }
      //   else {
      //       (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2, 0) else 0) // for LogicalRules.FrameUnfoldingFinal
      //     + (if (goal.post.hasOpBoolEq) math.pow(2,1) else 0) //for SubstRight
      //   }
      // }
      // else {0}

    val index2 = index1

    val index3 = index1

    val index4 =
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferCall(node)) {0} else {
            if (preferFrameAfterWrite(node)) {1} else {
              if (preferWriteAfterAlloc(node) || preferWriteIfPointers(goal)) {2} else {
                if (preferPickOrHeapUnifyPure(goal)) {3} else {
                  if (preferSubstRight(goal)) {4} else {5}
                }
              }
            }
          }
        } else
          (   (if (preferCall(node)) math.pow(2, 0) else 0)
            + (if (preferFrameAfterWrite(node)) math.pow(2, 1) else 0)
            + (if (preferWriteAfterAlloc(node) || preferWriteIfPointers(goal)) math.pow(2, 2) else 0)
            + (if (preferPickOrHeapUnifyPure(goal)) math.pow(2, 3) else 0)
            + (if (preferSubstRight(goal)) math.pow(2, 4) else 0)
        )
      } else {
        0
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

    val index = {0}

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
    val index = { 0
      //if (goal.env.runtime_rule_order_selection)
      //  (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2,0) else 0) // for LogicalRules.FrameFlat
      //else 0
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
        UnificationRules.HeapUnifyPointer
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

  //TODO: I should check
  // - frame
  // - write
  // - HeapUnifyPure or Pick
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
        if (config.delegatePure) DelegatePureSynthesis.PureSynthesisFinal else UnificationRules.Pick
      )
    //    ++
    //    (if (config.branchAbduction) List(UnificationRules.Pick) else List())

    val index = {0
    //  if (goal.env.runtime_rule_order_selection) {
    //    if (goal.env.fewer_feature_combinations) {
    //      if (node.isJustAfter(OperationalRules.WriteRule)) {0} else {
    //        if (node.isAfter(OperationalRules.ReadRule)) {1} else {2}
    //      }
    //    } else {
    //      (if (node.isAfter(OperationalRules.ReadRule)) math.pow(2,0) else 0) // OperationalRules.WriteRule
    //      + (if (node.isJustAfter(OperationalRules.WriteRule)) math.pow(2,1) else 0) // for LogicalRules.FrameFlat
    //    }
    //  }
    //  else {0}
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