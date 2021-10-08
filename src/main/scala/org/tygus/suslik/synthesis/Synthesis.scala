package org.tygus.suslik.synthesis

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.language.Statements.{Solution, _}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.{CyclicProofChecker, SMTSolving}
import org.tygus.suslik.report.{Log, ProofTrace}
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.SearchTree._
import org.tygus.suslik.synthesis.Termination._
import org.tygus.suslik.synthesis.rules.DelegatePureSynthesis
import org.tygus.suslik.synthesis.tactics.Tactic
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.util.SynStats

import scala.Console._
import scala.annotation.tailrec

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

class Synthesis(tactic: Tactic, implicit val log: Log, implicit val trace: ProofTrace) extends SepLogicUtils {

  def synthesizeProc(funGoal: FunSpec, env: Environment, sketch: Statement): (List[Procedure], SynStats) = {
    implicit val config: SynConfig = env.config
    implicit val stats: SynStats = env.stats
    val FunSpec(name, tp, formals, pre, post, var_decl) = funGoal

    if (!CyclicProofChecker.isConfigured()) {
      log.print(List((s"Cyclic proof checker is not configured! All termination check will be considered TRUE (this not sound).\n", Console.RED)))
    } else {
      log.print(List((s"The mighty cyclic proof checker is available. Well done!\n", Console.GREEN)))
    }

    if (config.delegatePure && !DelegatePureSynthesis.isConfigured()) {
      log.print(List((s"CVC4 is not available! All pure synthesis steps will be performed by enumeration (this takes more steps).\n", Console.RED)))
    }
    
    val goal = topLevelGoal(pre, post, formals, name, env, sketch, var_decl)
    log.print(List(("Initial specification:", Console.RESET), (s"${goal.pp}\n", Console.BLUE)))
    SMTSolving.init()
    memo.clear()
    ProofTrace.current = trace
    try {
      synthesize(goal)(stats = stats) match {
        case Some((body, helpers)) =>
          log.print(List((s"Succeeded leaves (${successLeaves.length}): ${successLeaves.map(n => s"${n.pp()}").mkString(" ")}", Console.YELLOW)))
          val main = Procedure(funGoal, body)
          (main :: helpers, stats)
        case None =>
          log.out.printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp}")
          (Nil, stats)
      }
    } catch {
      case SynTimeOutException(msg) =>
        log.out.printlnErr(msg)
        (Nil, stats)
    }
  }

  protected def synthesize(goal: Goal)
                          (stats: SynStats): Option[Solution] = {
    init(goal)
    processWorkList(stats, goal.env.config)
  }

  @tailrec final def processWorkList(implicit
                                     stats: SynStats,
                                     config: SynConfig): Option[Solution] = {
    // Check for timeouts
    if (!config.interactive && stats.timedOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut} seconds.\n")
    }

    val sz = worklist.length
    log.print(List((s"Worklist ($sz): ${worklist.map(n => s"${n.pp()}[${n.cost}]").mkString(" ")}", Console.YELLOW)))
    log.print(List((s"Succeeded leaves (${successLeaves.length}): ${successLeaves.map(n => s"${n.pp()}").mkString(" ")}", Console.YELLOW)))
    log.print(List((s"Memo (${memo.size}) Suspended (${memo.suspendedSize})", Console.YELLOW)))
    stats.updateMaxWLSize(sz)

    if (worklist.isEmpty) None // No more goals to try: synthesis failed
    else {
      val (node, addNewNodes) = popNode // Select next node to expand
      val goal = node.goal
      implicit val ctx: log.Context = log.Context(goal)
      stats.addExpandedGoal(node)
      log.print(List((s"Expand: ${node.pp()}[${node.cost}]", Console.YELLOW))) //      <goal: ${node.goal.label.pp}>
      if (config.printEnv) {
        log.print(List((s"${goal.env.pp}", Console.MAGENTA)))
      }
      log.print(List((s"${goal.pp}", Console.BLUE)))
      trace.add(node)

      // Lookup the node in the memo
      val res = memo.lookup(goal) match {
        case Some(Failed) => { // Same goal has failed before: record as failed
          log.print(List((s"Recalled FAIL", RED)))
          trace.add(node.id, Failed, Some("cache"))
          node.fail
          None
        }
        case Some(Succeeded(sol)) =>
        { // Same goal has succeeded before: return the same solution
          log.print(List((s"Recalled solution ${sol._1.pp}", RED)))
          // This seems to always hold in practice because we always get to the companion
          // before we get to any of its children;
          // if this ever fails, we can either:
          // 1. not recall solutions with outgoing backlinks or
          // 2. generate new transitions from these backlinks
//          assert(sol._1.companions.isEmpty, "Recalled solution with an outgoing backlink, this is unsound!")
          successLeaves = node :: successLeaves // Treat this node as a succeeded leaf
          trace.add(node.id, Succeeded(sol), Some("cache"))
          node.succeed(sol) match {
            case Left(sibling) => {
              worklist = addNewNodes(List(sibling))
              None
            }
            case Right(sol) => Some(sol)
          }
        }
        case Some(Expanded) => { // Same goal has been expanded before: wait until it's fully explored
          log.print(List(("Suspend", RED)))
          memo.suspend(node)
          worklist = addNewNodes(List(node))
          None
        }
        case None => expandNode(node, addNewNodes) // First time we see this goal: do expand
      }
      res match {
        case None => processWorkList
        case sol => sol
      }
    }
  }

  // Pop the next node to expand from the worklist;
  // return this node and a strategy for combining its children with the rest of the list
  protected def popNode(implicit config: SynConfig): (OrNode, Worklist => Worklist) =
    if (config.depthFirst) {// DFS? Pick the first one, insert new nodes in the front
      val best = worklist.head
      worklist = worklist.tail
      (best, _ ++ worklist)
    } else if (config.breadthFirst) { // BFS? Pick the first one non-suspended, insert new nodes in the back
      val best = worklist.minBy(n => memo.isSuspended(n))
      val idx = worklist.indexOf(best)
      worklist = worklist.take(idx) ++ worklist.drop(idx + 1)
      (best, worklist ++ _)
    } else { // Otherwise pick a minimum-cost node that is not suspended
      val best = worklist.minBy(n => (memo.isSuspended(n), n.cost))
      val idx = worklist.indexOf(best)
      worklist = worklist.take(idx) ++ worklist.drop(idx + 1)
      (best, worklist.take(idx) ++ _ ++ worklist.drop(idx))
    }

  // Expand node and return either a new worklist or the final solution
  protected def expandNode(node: OrNode, addNewNodes: List[OrNode] => List[OrNode])(implicit stats: SynStats,
                                                                                    config: SynConfig): Option[Solution] = {
    val goal = node.goal
    memo.save(goal, Expanded)
    implicit val ctx = log.Context(goal)

    // Apply all possible rules to the current goal to get a list of alternative expansions,
    // each of which can have multiple open subgoals
    val rulesAndWeights = tactic.nextRules(node)
    val allExpansionsAndWeights: Seq[(RuleResult, Double)] = applyRules(rulesAndWeights)(node, stats, config, ctx)
    val expansions: Seq[(RuleResult, Double)] = tactic.filterExpansions(allExpansionsAndWeights)

    // Check if any of the expansions is a terminal
    expansions.find(_._1.subgoals.isEmpty) match {
      case Some((e, _)) =>
        if (config.certTarget != null) {
          // [Certify]: Add a terminal node and its ancestors to the certification tree
          CertTree.addSuccessfulPath(node, e: RuleResult)
        }
        trace.add(e, node)
        successLeaves = node :: successLeaves
        node.succeed(e.producer(Nil)) match {
          case Left(sibling) => {
            // This node had a suspended and-sibling: add to the worklist
            worklist = addNewNodes(List(sibling))
            None
          }
          case Right(sol) => Some(sol) // This node had no more and-siblings: return solution
        }
      case None => { // no terminals: add all expansions to worklist
        // Create new nodes from the expansions
        val newNodes = for {
          ((e, w), i) <- expansions.zipWithIndex
          andNode = AndNode(i +: node.id, node, e): AndNode
          if isTerminatingExpansion(andNode) // termination check
          () = trace.add(andNode, andNode.nChildren)
        } yield {
          andNode.nextChild(w) // take the first goal from each new and-node; the first goal always exists
        }

        worklist = addNewNodes(newNodes.toList)
        if (newNodes.isEmpty) {
          // This is a dead-end: prune worklist and try something else
          log.print(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
          trace.add(node.id, Failed)
          node.fail
        } else {
          stats.addGeneratedGoals(newNodes.size)
        }
        None
      }
    }
  }


  protected def applyRules(rulesAndWeights: List[(SynthesisRule, Double)])(implicit node: OrNode,
                                                                 stats: SynStats,
                                                                 config: SynConfig,
                                                                 ctx: log.Context): Seq[(RuleResult, Double)] = {
    implicit val goal: Goal = node.goal
    rulesAndWeights match {
      case Nil => Vector() // No more rules to apply: done expanding the goal
      case (r, w) :: rsAndWs =>
        // Invoke the rule
        val ruleResults: Seq[RuleResult] = stats.recordRuleApplication(r.toString, r(goal))
        val children: Seq[(RuleResult, Double)] = ruleResults.map(result => (result, w))

        if (children.isEmpty) {
          // Rule not applicable: try other rules
          log.print(List((s"$r FAIL", RESET)), isFail = true)
          applyRules(rsAndWs)
        } else {
          // Rule applicable: try all possible sub-derivations
          val childFootprints = children.map(p => p._1).map(log.showChildren(goal))
          log.print(List((s"$r (${children.map(p =>p._1).size}): ${childFootprints.head}", RESET)))
          for {c <- childFootprints.tail}
            log.print(List((s" <|>  $c", CYAN)))

          if (r.isInstanceOf[InvertibleRule]) {
            // The rule is invertible: do not try other rules on this goal
            children
          } else {
            // Both this and other rules apply
            children ++ applyRules(rsAndWs)
          }
        }
    }
  }
}