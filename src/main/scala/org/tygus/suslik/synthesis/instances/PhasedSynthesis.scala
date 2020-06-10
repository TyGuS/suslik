package org.tygus.suslik.synthesis.instances

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.smt.SMTSolving.sat
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules.{GeneratesCode, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules._
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.util.SynLogging

class PhasedSynthesis(implicit val log: SynLogging) extends Synthesis {

  {
    // Warm-up the SMT solver on start-up to avoid future delays
    for (i <- 1 to 5; j <- 1 to 2; k <- 1 to 3) {
      sat(BinaryExpr(OpLeq, IntConst(i), BinaryExpr(OpPlus, IntConst(j), IntConst(k))))
    }
  }

  def nextRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    val config = goal.env.config
    if (goal.sketch != Hole)
    // Until we encounter a hole, symbolically execute the sketch
      anyPhaseRules(config).filterNot(_.isInstanceOf[GeneratesCode]) ++
        symbolicExecutionRules(config) ++
        specBasedRules(node).filterNot(_.isInstanceOf[GeneratesCode])
    else if (!config.phased)
    // Phase distinction is disabled: use all non top-level rules
      anyPhaseRules(config) ++ unfoldingPhaseRules(config) ++
        postBlockPhaseRules(config) ++ preBlockPhaseRules(config) ++
        pointerPhaseRules(config) ++ purePhaseRules(config)
    else anyPhaseRules(config) ++ specBasedRules(node)
  }

  def specBasedRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    val config = goal.env.config
    if (node.parent.isDefined && node.parent.get.rule == AbduceCall && node.id.head > 0)
    // TODO: This is a hack: AbduceCall does not make progress,
    // and hence has to be followed by Call, otherwise synthesis gets stuck.
    // Proper fix: merge the two rules
      List(CallRule)
    else if (goal.hasPredicates()) (
      // Only if can unfold further
      // Unfolding phase: get rid of predicates
      unfoldingPhaseRules(config) 
        /* TODO [Mutual]:
           Enabling the following rules progresses the synthesis of `rose_tree_free` even further,
           but makes other case studies excruciatingly slow, so I comment it for now.
            
           This is sub-optimal, and ideally we only need to check for predicates
           that still cna be unfolded. However, introducing this more elaborated check
           vai goal.hasViablePredicates breaks the synthesis down the line.
           
           I need this to enable cyclic synthesis for rose tree    
         */
        // ++ preBlockPhaseRules(config)
      )
    else if (goal.post.hasBlocks)
    // Block phase: get rid of blocks
      postBlockPhaseRules(config)
    else if (goal.hasBlocks)
      preBlockPhaseRules(config)
    else if (goal.hasExistentialPointers)
    // Pointer phase: match all existential pointers
      pointerPhaseRules(config)
    else
    // Pure phase: get rid of all the heap
      purePhaseRules(config)
  }

  def anyPhaseRules(config: SynConfig): List[SynthesisRule] = List(
    LogicalRules.StarPartial,
    LogicalRules.NilNotLval,
    LogicalRules.Inconsistency,
    if (!config.fail) FailRules.Noop else FailRules.PostInconsistent,
    OperationalRules.ReadRule,
    //    LogicalRules.SubstLeft,
  )

  def symbolicExecutionRules(config: SynConfig): List[SynthesisRule] = List(
    SymbolicExecutionRules.Open,
    SymbolicExecutionRules.GuidedRead,
    SymbolicExecutionRules.GuidedWrite,
    SymbolicExecutionRules.GuidedAlloc,
    SymbolicExecutionRules.GuidedFree,
    SymbolicExecutionRules.Conditional,
    SymbolicExecutionRules.GuidedCall,
    //    LogicalRules.EmpRule,
    //    LogicalRules.StarPartial,
    //    LogicalRules.NilNotLval,
    //    LogicalRules.Inconsistency,
    //    if (!config.fail) FailRules.Noop else FailRules.PostInconsistent,
    //    LogicalRules.SubstLeftVar,
    //    LogicalRules.FrameUnfolding,
    //    UnificationRules.HeapUnifyUnfolding,
    //    UnfoldingRules.Close,
    //    LogicalRules.FrameBlock,
    //    UnificationRules.HeapUnifyBlock,
    //    LogicalRules.SubstLeft,
    //    UnificationRules.SubstRight,
    //    LogicalRules.FrameFlat,
    //    UnificationRules.HeapUnifyPointer,
    //    if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,
    //    UnificationRules.HeapUnifyPure,
    ////    UnificationRules.PureUnify,
    //    UnificationRules.Pick,
    ////    UnificationRules.PickFromEnvRule
  )

  def unfoldingPhaseRules(config: SynConfig): List[SynthesisRule] = List(
    LogicalRules.SubstLeftVar,
    //    LogicalRules.SubstRightVar,
    LogicalRules.FrameUnfolding,
    UnfoldingRules.CallRule,
    UnfoldingRules.Open,
    UnificationRules.HeapUnifyUnfolding,
    UnfoldingRules.AbduceCall,
    UnfoldingRules.Close,
  )

  def postBlockPhaseRules(config: SynConfig): List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else if (!config.fail) FailRules.Noop else FailRules.PostInvalid,
    LogicalRules.FrameBlock,
    UnificationRules.HeapUnifyBlock,
    OperationalRules.AllocRule
  )

  def preBlockPhaseRules(config: SynConfig): List[SynthesisRule] = List(
    OperationalRules.FreeRule
  )

  def pointerPhaseRules(config: SynConfig): List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else if (!config.fail) FailRules.Noop else FailRules.PostInvalid,
    if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    OperationalRules.WriteRule,
    UnificationRules.HeapUnifyPointer,
  )

  def purePhaseRules(config: SynConfig): List[SynthesisRule] = List(
    if (config.branchAbduction) FailRules.AbduceBranch else if (!config.fail) FailRules.Noop else FailRules.PostInvalid,
    LogicalRules.EmpRule,
    if (!config.fail) FailRules.Noop else FailRules.HeapUnreachable,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.FrameFlat,
    OperationalRules.WriteRule,
    //    UnificationRules.PureUnify,
    UnificationRules.HeapUnifyPure,
    UnificationRules.Pick,
  )

}
