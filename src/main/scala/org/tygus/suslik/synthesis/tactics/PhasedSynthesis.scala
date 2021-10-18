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
import org.tygus.suslik.synthesis.Memoization._

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
    (goal.post.phi.conjuncts.exists(_.isOpEq) || goal.post.phi.conjuncts.exists(_.isOpBoolEq)) &&
      goal.existentials.exists(existential => goal.post.phi.vars.contains(existential))
  }

  // equality in the pure part of the pre-condition
  def preferSubstLeft(goal: Goal) = {
    (goal.pre.phi.conjuncts.exists(_.isOpEq)) || (goal.pre.phi.conjuncts.exists(_.isOpBoolEq))
  }

  // both pre- and post-conditions are empty
  def preferEmp(goal: Goal) = goal.pre.sigma.isEmp && goal.post.sigma.isEmp

  // just after a write rule
  def preferFrameAfterWrite(node: OrNode) = {
    ((node.isJustAfter(OperationalRules.WriteRule)) || (node.isJustAfter(LogicalRules.GhostWrite))) &&
      (!(memo.isSuspended(node))) // We don't want to frame after write if we are doing an abduce call.
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
    (node.isJustAfter(UnificationRules.HeapUnifyUnfolding)) ||
    (node.isJustAfter(UnificationRules.HeapUnifyBlock)) ||
    (node.isJustAfter(UnificationRules.HeapUnifyPointer))
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

  def preferClose(node: OrNode): Boolean =
    node.isAfter(UnfoldingRules.Open) && !(node.isAfter(UnfoldingRules.Close))

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

  def nextRules(node: OrNode): List[(SynthesisRule, Double)] = {

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

      //TODO: use the value from evolutionary.py instead of the hard-coded 1.0
      anyPhaseRulesOrSpecBasedRulesNested.flatten: List[(SynthesisRule, Double)]

    }

    def sketchHole = {

      val index = 0
      val ordersOfSketchHole = goal.env.ordersOfSketchHole
      val orderOfSketchHole = ordersOfSketchHole.apply(index.toInt)

      val unOrderedSketchHole =
        List (
          anyPhaseRules(node).filterNot(_._1.isInstanceOf[GeneratesCode]),
          symbolicExecutionRules(goal),
          specBasedRules(node).filterNot(_._1.isInstanceOf[GeneratesCode])
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

  def filterExpansions(allExpansions: Seq[(RuleResult, Double)]): Seq[(RuleResult, Double)] = allExpansions

  protected def specBasedRules(node: OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal

    if (goal.hasPredicates()) {
      // Unfolding phase: get rid of predicates
      val lastUnfoldingRule = node.ruleHistory.dropWhile(anyPhaseRules(node).contains).headOption
      if (lastUnfoldingRule.contains(HeapUnifyUnfolding) ||
        lastUnfoldingRule.contains(FrameUnfolding) ||
        lastUnfoldingRule.contains(FrameUnfoldingFinal))
        unfoldingNoUnfoldPhaseRules(node)
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

  protected def anyPhaseRules(node:OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal

    val index = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferBranch(node)) {0} else {
            if (preferInconsistency(node) || preferStarPartial(goal)) {1} else {
                if (preferReadRule(goal)) {2} else {
                  if (preferSubstRight(goal) || preferSubstLeft(goal)) {3} else {4}
                }
              }
          }
        }
        else {
            (if (preferBranch(node)) {math.pow(2,0)} else {0})
          + (if (preferInconsistency(node) || preferStarPartial(goal)) {math.pow(2,1)} else {0})
          + (if (preferReadRule(goal)) {math.pow(2,2)} else {0})
          + (if (preferSubstRight(goal) || preferSubstLeft(goal)) {math.pow(2,3)} else {0})
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
      OperationalRules.ReadRule,
      BranchRules.Branch
    )

    val weightOfAnyPhaseRules = goal.env.weightsOfAnyPhaseRules.apply(index.toInt)
    val unorderedPairedAnyPhaseRules = unorderedAnyPhaseRules zip weightOfAnyPhaseRules

    if (goal.env.config.evolutionary) {
      List(
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(0)),
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(1)),
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(2)),
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(3)),
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(4)),
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(5)),
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(6)),
        unorderedPairedAnyPhaseRules(orderOfAnyPhaseRules.apply(7))
      )
    } else
      List(unorderedPairedAnyPhaseRules:_*)
  }

  protected def symbolicExecutionRules(goal:Goal): List[(SynthesisRule, Double)] = {

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

    val weightsOfSymbolicExecutionRules= goal.env.weightsOfSymbolicExecutionRules.apply(index.toInt)
    val unorderedPairedSymbolicExecutionRules = unOrderedSymbolicExecutionRules zip weightsOfSymbolicExecutionRules

    if (goal.env.config.evolutionary) {
      List(
        unorderedPairedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(0)),
        unorderedPairedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(1)),
        unorderedPairedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(2)),
        unorderedPairedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(3)),
        unorderedPairedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(4)),
        unorderedPairedSymbolicExecutionRules(orderOfSymbolicExecutionRules.apply(5))
      )
    } else
      List(unorderedPairedSymbolicExecutionRules:_*)
  }

  protected def unfoldingPhaseRules(node:OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal
    //TODO: check for a predicate in the post and Open in the past
    val index = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferFrameAfterUnifyHeap(node)) {0} else {
            if (preferUnifyHeap(goal)) {1} else {
              if (preferClose(node)) {2} else {3}
              }
            }
          }
        else {
          (if (preferFrameAfterUnifyHeap(node)) {math.pow(2,0)} else {0})
          + (if (preferUnifyHeap(goal)) {math.pow(2,1)} else {0})
          + (if (preferClose(node)) {math.pow(2,2)} else {0})
        }
      }
      else 0
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

    val weightsOfUnfoldingPhaseRules = goal.env.weightsOfUnfoldingPhaseRules.apply(index.toInt)
    val unorderedPairedUnfoldingPhaseRules = unOrderedUnfoldingPhaseRules zip weightsOfUnfoldingPhaseRules

    if (goal.env.config.evolutionary) {
      List(
        unorderedPairedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(0)),
        unorderedPairedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(1)),
        unorderedPairedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(2)),
        unorderedPairedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(3)),
        unorderedPairedUnfoldingPhaseRules(orderOfUnfoldingPhaseRules.apply(4))
      )
    } else
      List(unorderedPairedUnfoldingPhaseRules:_*)
  }

  protected def unfoldingPostPhaseRules(node: OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal
    val index = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferFrameAfterUnifyHeap(node)) {0} else {
            if (preferUnifyHeap(goal)) {1} else {
              if (preferClose(node)) {2} else {3}
            }
          }
        }
        else {
          (if (preferFrameAfterUnifyHeap(node)) {math.pow(2,0)} else {0})
          + (if (preferUnifyHeap(goal)) {math.pow(2,1)} else {0})
          + (if (preferClose(node)) {math.pow(2,2)} else {0})
        }
      }
      else 0
    }

    val unOrderedUnfoldingPostPhaseRules =
      List(
        LogicalRules.FrameUnfoldingFinal,
        UnificationRules.HeapUnifyUnfolding,
        UnfoldingRules.Close,
      )

    val weightsOfUnfoldingPostPhaseRules = goal.env.weightsOfUnfoldingPostPhaseRules.apply(index.toInt)
    val unorderedPairedUnfoldingPostPhaseRules = unOrderedUnfoldingPostPhaseRules zip weightsOfUnfoldingPostPhaseRules

    val ordersOfUnfoldingPostPhaseRules = goal.env.ordersOfUnfoldingPostPhaseRules
    val orderOfUnfoldingPostPhaseRules = ordersOfUnfoldingPostPhaseRules.apply(index.toInt)

    if (goal.env.config.evolutionary) {
      List(
        unorderedPairedUnfoldingPostPhaseRules(orderOfUnfoldingPostPhaseRules.apply(0)),
        unorderedPairedUnfoldingPostPhaseRules(orderOfUnfoldingPostPhaseRules.apply(1)),
        unorderedPairedUnfoldingPostPhaseRules(orderOfUnfoldingPostPhaseRules.apply(2))
      )
    } else
      List(unorderedPairedUnfoldingPostPhaseRules:_*)

  }

  protected def unfoldingNoUnfoldPhaseRules(node: OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal
    val index = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferFrameAfterUnifyHeap(node)) {0} else {
            if (preferUnifyHeap(goal)) {1} else {
              2
            }
          }
        }
        else {
          (if (preferFrameAfterUnifyHeap(node)) {math.pow(2,0)} else {0})
          + (if (preferUnifyHeap(goal)) {math.pow(2,1)} else {0})
        }
      }
      else 0
    }

    val unOrderedUnfoldingNoUnfoldPhaseRules =
      Vector (
        LogicalRules.FrameUnfoldingFinal,
        UnificationRules.HeapUnifyUnfolding
      )

    val weightsOfUnfoldingNoUnfoldPhaseRules = goal.env.weightsOfUnfoldingNoUnfoldPhaseRules.apply(index.toInt)
    val unorderedPairedUnfoldingNoUnfoldPhaseRules = unOrderedUnfoldingNoUnfoldPhaseRules zip weightsOfUnfoldingNoUnfoldPhaseRules

    val ordersOfUnfoldingNoUnfoldPhaseRules = goal.env.ordersOfUnfoldingNoUnfoldPhaseRules
    val orderOfUnfoldingNoUnfoldPhaseRules = ordersOfUnfoldingNoUnfoldPhaseRules.apply(index.toInt)

    if (goal.env.config.evolutionary)
      List(
        unorderedPairedUnfoldingNoUnfoldPhaseRules(orderOfUnfoldingNoUnfoldPhaseRules.apply(0)),
        unorderedPairedUnfoldingNoUnfoldPhaseRules(orderOfUnfoldingNoUnfoldPhaseRules.apply(1))
      )
    else
      List(unorderedPairedUnfoldingNoUnfoldPhaseRules:_*)

  }

  protected def callAbductionRules(node: OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal

    val index1 = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferFrameAfterUnifyHeap(node)) {0} else {
            if (preferUnifyHeap(goal)) {1} else {
              if(preferSubstRight(goal)) {2} else {3}
            }
          }
        }
        else {
          (if (preferFrameAfterUnifyHeap(node)) {math.pow(2,0)} else {0})
          + (if (preferUnifyHeap(goal)) {math.pow(2,1)} else {0})
          + (if (preferSubstRight(goal)) {math.pow(2,2)} else {0})
        }
      }
      else 0
    }

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
    val unOrderedCallAbductionRulesNested1: Vector[SynthesisRule] =
          Vector(
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            LogicalRules.FrameUnfoldingFinal,
            UnificationRules.HeapUnifyUnfolding)
    val weightsOfCallAbductionRules1 = goal.env.weightsOfCallAbductionRules1.apply(index1.toInt)
    val unorderedPairedCallAbductionRules1 = unOrderedCallAbductionRulesNested1 zip weightsOfCallAbductionRules1

    val ordersOfCallAbductionRules2 = goal.env.ordersOfCallAbductionRules2
    val orderOfCallAbductionRules2 = ordersOfCallAbductionRules2.apply(index2.toInt)
    val unOrderedCallAbductionRulesNested2: Vector[SynthesisRule] =
      Vector(
        UnificationRules.SubstRight,
        FailRules.PostInconsistent,
        FailRules.CheckPost,
        LogicalRules.FrameBlock,
        UnificationRules.HeapUnifyBlock
      )
    val weightsOfCallAbductionRules2 = goal.env.weightsOfCallAbductionRules2.apply(index2.toInt)
    val unorderedPairedCallAbductionRules2 = unOrderedCallAbductionRulesNested2 zip weightsOfCallAbductionRules2

    val ordersOfCallAbductionRules3 = goal.env.ordersOfCallAbductionRules3
    val orderOfCallAbductionRules3 = ordersOfCallAbductionRules3.apply(index3.toInt)
    val unOrderedCallAbductionRulesNested3: Vector[SynthesisRule] =
      Vector(
        UnificationRules.SubstRight,
        FailRules.PostInconsistent,
        FailRules.CheckPost,
        LogicalRules.FrameFlat,
        UnificationRules.HeapUnifyPointer
      )
    val weightsOfCallAbductionRules3 = goal.env.weightsOfCallAbductionRules3.apply(index3.toInt)
    val unorderedPairedCallAbductionRules3 = unOrderedCallAbductionRulesNested3 zip weightsOfCallAbductionRules3

    val ordersOfCallAbductionRules4 = goal.env.ordersOfCallAbductionRules4
    val orderOfCallAbductionRules4 = ordersOfCallAbductionRules4.apply(index4.toInt)
    val unOrderedCallAbductionRulesNested4: Vector[SynthesisRule] =
          Vector(
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            UnfoldingRules.CallRule,
            LogicalRules.FrameFlat,
            UnificationRules.PickArg,
            UnificationRules.PickCard,
            LogicalRules.GhostWrite,
            UnificationRules.HeapUnifyPure,
            LogicalRules.SimplifyConditional,
            OperationalRules.WriteRule,
            UnificationRules.Pick
          )
    val weightsOfCallAbductionRules4 = goal.env.weightsOfCallAbductionRules4.apply(index4.toInt)
    val unorderedPairedCallAbductionRules4 = unOrderedCallAbductionRulesNested4 zip weightsOfCallAbductionRules4

    val defaultPairedOrderedCallAbductionRules =
       (if (goal.post.sigma.apps.nonEmpty)
          List(
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            LogicalRules.FrameUnfoldingFinal,
            UnificationRules.HeapUnifyUnfolding
          ) zip weightsOfCallAbductionRules1
        else if (goal.post.sigma.blocks.nonEmpty)
          List(
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            LogicalRules.FrameBlock,
            UnificationRules.HeapUnifyBlock,
          ) zip weightsOfCallAbductionRules2
        else if (goal.hasExistentialPointers)
          List(
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            LogicalRules.FrameFlat,
            UnificationRules.HeapUnifyPointer
          ) zip weightsOfCallAbductionRules3
        else
          List(
            UnificationRules.SubstRight,
            FailRules.PostInconsistent,
            FailRules.CheckPost,
            UnfoldingRules.CallRule,
            LogicalRules.FrameFlat,
            UnificationRules.PickArg,
            UnificationRules.PickCard,
            LogicalRules.GhostWrite,
            UnificationRules.HeapUnifyPure,
            LogicalRules.SimplifyConditional,
            OperationalRules.WriteRule,
            UnificationRules.Pick
          ) zip weightsOfCallAbductionRules4
         )

    val orderedCallAbductionRulesNested =
      if (goal.env.config.evolutionary)
        (if (goal.post.sigma.apps.nonEmpty)
          List(
            unorderedPairedCallAbductionRules1(orderOfCallAbductionRules1.apply(0)),
            unorderedPairedCallAbductionRules1(orderOfCallAbductionRules1.apply(1)),
            unorderedPairedCallAbductionRules1(orderOfCallAbductionRules1.apply(2)),
            unorderedPairedCallAbductionRules1(orderOfCallAbductionRules1.apply(3)),
            unorderedPairedCallAbductionRules1(orderOfCallAbductionRules1.apply(4))
          )
        else if (goal.post.sigma.blocks.nonEmpty)
          List(
            unorderedPairedCallAbductionRules2(orderOfCallAbductionRules2.apply(0)),
            unorderedPairedCallAbductionRules2(orderOfCallAbductionRules2.apply(1)),
            unorderedPairedCallAbductionRules2(orderOfCallAbductionRules2.apply(2)),
            unorderedPairedCallAbductionRules2(orderOfCallAbductionRules2.apply(3)),
            unorderedPairedCallAbductionRules2(orderOfCallAbductionRules2.apply(4))
          )
        else if (goal.hasExistentialPointers)
          List(
            unorderedPairedCallAbductionRules3(orderOfCallAbductionRules3.apply(0)),
            unorderedPairedCallAbductionRules3(orderOfCallAbductionRules3.apply(1)),
            unorderedPairedCallAbductionRules3(orderOfCallAbductionRules3.apply(2)),
            unorderedPairedCallAbductionRules3(orderOfCallAbductionRules3.apply(3)),
            unorderedPairedCallAbductionRules3(orderOfCallAbductionRules3.apply(4))
          )
        else
          List(
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(0)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(1)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(2)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(3)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(4)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(5)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(6)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(7)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(8)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(9)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(10)),
            unorderedPairedCallAbductionRules4(orderOfCallAbductionRules4.apply(11))
          )
          )
      else
        defaultPairedOrderedCallAbductionRules

    orderedCallAbductionRulesNested
  }

  protected def postBlockPhaseRules(goal: Goal): List[(SynthesisRule, Double)] = {

    val index = {0}

    val unOrderedOfPostBlockPhaseRules =
      Vector(
        (if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost),
        LogicalRules.FrameBlock,
        UnificationRules.HeapUnifyBlock,
        OperationalRules.AllocRule
      )

    val weightsOfPostBlockPhaseRules = goal.env.weightsOfPostBlockPhaseRules.apply(index.toInt)
    val unorderedPairedPostBlockPhaseRules = unOrderedOfPostBlockPhaseRules zip weightsOfPostBlockPhaseRules

    val ordersOfPostBlockPhaseRules = goal.env.ordersOfPostBlockPhaseRules
    val orderOfPostBlockPhaseRules = ordersOfPostBlockPhaseRules.apply(index.toInt)

    if (goal.env.config.evolutionary)
      List(
        unorderedPairedPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(0)),
        unorderedPairedPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(1)),
        unorderedPairedPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(2)),
        unorderedPairedPostBlockPhaseRules(orderOfPostBlockPhaseRules.apply(3))
      )
    else List(unorderedPairedPostBlockPhaseRules:_*)
  }

  protected def preBlockPhaseRules: List[(SynthesisRule, Double)] = List(
    (OperationalRules.FreeRule, 1.0)//TODO
  )

  protected def pointerPhaseRules(node:OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal

    val index = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferFrameAfterWrite(node)) {0} else {
            if (preferFrameAfterUnifyHeap(node)) {1} else {
              if (preferUnifyHeap(goal)) {2} else {3
              }
            }
          }
        }
        else {
          (   (if (preferFrameAfterWrite(node)) math.pow(2,0) else 0)
            + (if (preferFrameAfterUnifyHeap(node)) math.pow(2,1) else 0)
            + (if (preferUnifyHeap(goal)) math.pow(2,2) else 0)
            )
        }
      } else 0
    }

    val unOrderedPointerPhaseRules =
      Vector(
        if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost,
        FailRules.HeapUnreachable,
        LogicalRules.FrameFlat,
        UnificationRules.HeapUnifyPointer
      )

    val weightsOfPointerPhaseRules = goal.env.weightsOfPointerPhaseRules.apply(index.toInt)
    val unorderedPairedPointerPhaseRules = unOrderedPointerPhaseRules zip weightsOfPointerPhaseRules

    val ordersOfPointerPhaseRules = goal.env.ordersOfPointerPhaseRules
    val orderOfPointerPhaseRules = ordersOfPointerPhaseRules.apply(index.toInt)

    if (goal.env.config.evolutionary)
      List(
        unorderedPairedPointerPhaseRules(orderOfPointerPhaseRules.apply(0)),
        unorderedPairedPointerPhaseRules(orderOfPointerPhaseRules.apply(1)),
        unorderedPairedPointerPhaseRules(orderOfPointerPhaseRules.apply(2)),
        unorderedPairedPointerPhaseRules(orderOfPointerPhaseRules.apply(3))
      )
    else List(unorderedPairedPointerPhaseRules:_*)

  }

  protected def purePhaseRules(node: OrNode): List[(SynthesisRule, Double)] = {

    val goal = node.goal

    val index = {
      if (goal.env.runtime_rule_order_selection) {
        if (goal.env.fewer_feature_combinations) {
          if (preferFrameAfterWrite(node)) {0} else {
            if (preferWriteIfPointers(goal)) {1} else {
              if (preferWriteAfterAlloc(node)) {2} else {
                if (preferPickOrHeapUnifyPure(goal)) {3} else {
                  4
                }
              }
            }
          }
        } else {
          (if (preferFrameAfterWrite(node)) math.pow(2,0) else 0)
          + (if (preferWriteIfPointers(goal)) math.pow(2,1) else 0)
          + (if (preferWriteAfterAlloc(node)) math.pow(2,2) else 0)
          + (if (preferPickOrHeapUnifyPure(goal)) math.pow(2,3) else 0)
        }
      }
      else {0}
    }

    val unorderedPurePhaseRules =
      Vector(
        if (config.branchAbduction) BranchRules.AbduceBranch else FailRules.CheckPost,
        LogicalRules.EmpRule,
        FailRules.HeapUnreachable,
        LogicalRules.FrameFlat,
        UnificationRules.PickCard,
        LogicalRules.GhostWrite,
        UnificationRules.HeapUnifyPure,
        LogicalRules.SimplifyConditional,
        OperationalRules.WriteRule,
        if (config.delegatePure) DelegatePureSynthesis.PureSynthesisFinal else UnificationRules.Pick
      )

    val weightsOfPurePhaseRules = goal.env.weightsOfPurePhaseRules.apply(index.toInt)
    val unorderedPairedPurePhaseRules = unorderedPurePhaseRules zip weightsOfPurePhaseRules

    val ordersOfPurePhaseRules = goal.env.ordersOfPurePhaseRules
    val orderOfPurePhaseRules = ordersOfPurePhaseRules.apply(index.toInt)

    if (goal.env.config.evolutionary) {
      List(
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(0)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(1)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(2)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(3)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(4)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(5)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(6)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(7)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(8)),
        unorderedPairedPurePhaseRules(orderOfPurePhaseRules.apply(9))
      )
    } else
      List(unorderedPairedPurePhaseRules:_*)

  }

}