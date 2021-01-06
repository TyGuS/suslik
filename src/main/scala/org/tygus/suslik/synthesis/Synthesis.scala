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
import scala.collection.mutable

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

class Synthesis(tactic: Tactic, implicit val log: Log, implicit val trace: ProofTrace) extends SepLogicUtils {
  import log.out.testPrintln
  def synthesizeProc(funGoal: FunSpec, env: Environment, sketch: Statement): (List[Procedure], SynStats,  Option[mutable.Map[MemoGoal, GoalStatus]] ) = {
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

    if (config.enumeration) {
      log.print((List((s"Helasdfdsaflo\n", Console.RED))))
      testPrintln(s"Hello")
    }
    val goal = topLevelGoal(pre, post, formals, name, env, sketch, var_decl)
    log.print(List(("Initial specification:", Console.RESET), (s"${goal.pp}\n", Console.BLUE)))
    SMTSolving.init()
    memo.clear()
    ProofTrace.current = trace
    try {
      synthesize(goal)(stats = stats) match {
        case (Some((body, helpers)), cache) =>
          testPrintln(s"Succeeded leaves (${successLeaves.length}): ${successLeaves.map(n => s"${n.pp()}").mkString(" ")})")
          val main = Procedure(funGoal, body)
          (main :: helpers, stats, Some(cache))
        case (None, _) =>
          log.out.printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp}")
          (Nil, stats, None)

      }
    } catch {
      case SynTimeOutException(msg) =>
        log.out.printlnErr(msg)
        (Nil, stats, None)
    }
  }

  protected def synthesize(goal: Goal)
                          (stats: SynStats): (Option[Solution],  mutable.Map[MemoGoal, GoalStatus] ) = {
    // initialize goal as an OrNode
    init(goal)
    // process work list which is a singleton containing OrNode(goal)
    processWorkList(stats, goal.env.config)
  }

  @tailrec final def processWorkList(implicit
                                     stats: SynStats,
                                     config: SynConfig): (Option[Solution],  mutable.Map[MemoGoal, GoalStatus] ) = {
    // Check for timeouts
    if (!config.interactive && stats.timedOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut} seconds.\n")
    }
    val sz = worklist.length
    log.print(List((s"Worklist ($sz): ${worklist.map(n => s"${n.pp()}[${n.cost}]").mkString(" ")}", Console.YELLOW)))
    log.print(List((s"Succeeded leaves (${successLeaves.length}): ${successLeaves.map(n => s"${n.pp()}").mkString(" ")}", Console.YELLOW)))
    log.print(List((s"Memo (${memo.size}) Suspended (${memo.suspendedSize})", Console.YELLOW)))
    stats.updateMaxWLSize(sz)

    if (worklist.isEmpty) (None, mutable.Map.empty) // No more goals to try: synthesis failed
    else {
      val (node, addNewNodes) = selectNode // Select next node to expand based on DFS/BFS/Min-cost
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
          worklist = addNewNodes(Nil)
          node.fail
          None
        }
        case Some(Succeeded(sol)) =>
        { // Same goal has succeeded before: return the same solution
          log.print(List((s"Recalled solution ${sol._1.pp}", RED)))
          trace.add(node.id, Succeeded(sol), Some("cache"))
          worklist = addNewNodes(Nil)
          node.succeed(sol)
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
        case sol => {
//          testPrintln(s"Success leaves: ${successLeaves.toString()} ")
//          for (on <- successLeaves){
//            testPrintln("SDFSADF")
//            testPrintln(on.pp())
//          }
          (sol, memo.returnCache)
        }
      }
    }
  }

  // Given a worklist, return the next node to work on
  // and a strategy for combining its children with the rest of the list
  protected def selectNode(implicit config: SynConfig): (OrNode, Worklist => Worklist) =
    if (config.depthFirst) // DFS? Pick the first one, insert new nodes in the front
      (worklist.head, _ ++ worklist.tail)
    else if (config.breadthFirst) { // BFS? Pick the first one non-suspended, insert new nodes in the back
      val best = worklist.minBy(n => memo.isSuspended(n))
      val idx = worklist.indexOf(best)
      (best, worklist.take(idx) ++ worklist.drop(idx + 1) ++ _)
    } else { // Otherwise pick a minimum-cost node that is not suspended
      val best = worklist.minBy(n => (memo.isSuspended(n), n.cost))
      val idx = worklist.indexOf(best)
      (best, worklist.take(idx) ++ _ ++ worklist.drop(idx + 1))
    }

  var store: List[Option[(Statement, List[Procedure])]] = List[Option[(Statement, List[Procedure])]]()

  // Expand node and return either a new worklist or the final solution
  protected def expandNode(node: OrNode, addNewNodes: List[OrNode] => List[OrNode])(implicit stats: SynStats,
                                                                                    config: SynConfig): Option[Solution] = {
    val goal = node.goal
    memo.save(goal, Expanded)
    implicit val ctx = log.Context(goal)

    // Apply all possible rules to the current goal to get a list of alternative expansions,
    // each of which can have multiple open subgoals
    // rules are any phased rules since our sketch is a Hole and we set phased config to true.
    val rules = tactic.nextRules(node)
    val allExpansions = applyRules(rules)(node, stats, config, ctx)
    // no filtering is done for Phased strategy
    val expansions = tactic.filterExpansions(allExpansions)
    // Check if any of the expansions is a terminal
    expansions.find(_.subgoals.isEmpty) match {
      case Some(e) =>
        if (config.certTarget != null) {
          // [Certify]: Add a terminal node and its ancestors to the certification tree
          CertTree.addSuccessfulPath(node, e)
        }
        trace.add(e, node)
        successLeaves = node :: successLeaves
        worklist = addNewNodes(Nil)
        val sol = node.succeed(e.producer(Nil))
        sol
      case None => { // no terminals: add all expansions to worklist
        // Create new nodes from the expansions
        val newNodes = for {
          (e, i) <- expansions.zipWithIndex
          andNode = AndNode(i +: node.id, node, e)
          if isTerminatingExpansion(andNode) // termination check
          nSubs = e.subgoals.size; () = trace.add(andNode, nSubs)
          (g, j) <- if (nSubs == 1) List((e.subgoals.head, -1)) // this is here only for logging
          else e.subgoals.zipWithIndex
        } yield {
          val extraCost = if (j == -1) 0 else e.subgoals.drop(j + 1).map(_.cost).sum
          OrNode(j +: andNode.id, g, Some(andNode), node.extraCost + extraCost)
        }

        // Suspend nodes with older and-siblings
        newNodes.foreach(n => {
          val idx = n.childIndex
          if (idx > 0) {
            val sib = newNodes.find(s => s.parent == n.parent && s.childIndex == idx - 1).get
            log.print(List((s"Suspending ${n.pp()} until ${sib.pp()} succeeds", RED)))
            memo.suspendSibling(n, sib) // always process the left and-goal first; unsuspend next once it succeeds
          }
        })

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


  protected def applyRules(rules: List[SynthesisRule])(implicit node: OrNode,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ctx: log.Context): Seq[RuleResult] = {
    implicit val goal: Goal = node.goal
    rules match {
      case Nil => Vector() // No more rules to apply: done expanding the goal
      case r :: rs =>
        // Invoke the rule
        val children = stats.recordRuleApplication(r.toString, r(goal))

        if (children.isEmpty) {
          // Rule not applicable: try other rules
          log.print(List((s"$r FAIL", RESET)), isFail = true)
          applyRules(rs)
        } else {
          // Rule applicable: try all possible sub-derivations
          val childFootprints = children.map(log.showChildren(goal))
          log.print(List((s"$r (${children.size}): ${childFootprints.head}", RESET)))
          for {c <- childFootprints.tail}
            log.print(List((s" <|>  $c", CYAN)))

          if (r.isInstanceOf[InvertibleRule]) {
            // The rule is invertible: do not try other rules on this goal
            children
          } else {
            // Both this and other rules apply
            children ++ applyRules(rs)
          }
        }
    }
  }
}