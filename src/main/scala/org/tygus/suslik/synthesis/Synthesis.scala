package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.{Solution, _}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.{SApp, _}
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.SearchTree._
import org.tygus.suslik.util.{SynLogging, SynStats}
import org.tygus.suslik.synthesis.rules.Rules._

import scala.Console._
import scala.annotation.tailrec

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis extends HasMemo with SepLogicUtils {

  val log: SynLogging

  import log._

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  def nextRules(node: OrNode): List[SynthesisRule]

  def synthesizeProc(funGoal: FunSpec, env: Environment, sketch: Statement): (List[Procedure], SynStats) = {
    implicit val config: SynConfig = env.config
    val FunSpec(name, tp, formals, pre, post, var_decl) = funGoal
    val goal = topLevelGoal(pre, post, formals, name, env, sketch, var_decl)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))
    val stats = new SynStats()
    SMTSolving.init()
    try {
      synthesize(goal)(stats = stats) match {
        case Some((body, helpers)) =>
          val main = Procedure(name, tp, formals, body)
          (main :: helpers, stats)
        case None =>
          printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp}")
          (Nil, stats)
      }
    } catch {
      case SynTimeOutException(msg) =>
        printlnErr(msg)
        (Nil, stats)
    }
  }

  protected def synthesize(goal: Goal)
                          (stats: SynStats): Option[Solution] = {
    // Initialize worklist: root or-node containing the top-level goal
    val root = OrNode(Vector(), goal, None, goal.allHeaplets)
    clearMemo(root)
    val worklist = List(root)
    processWorkList(worklist)(stats, goal.env.config)
  }

  @tailrec final def processWorkList(worklist: List[OrNode])
                                    (implicit
                                     stats: SynStats,
                                     config: SynConfig): Option[Solution] = {
    // Check for timeouts
    val currentTime = System.currentTimeMillis()
    if (currentTime - config.startTime > config.timeOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut.toDouble / 1000} seconds.\n")
    }

    val sz = worklist.length
    printLog(List((s"Worklist ($sz): ${worklist.map(_.pp()).mkString(" ")}", Console.YELLOW)))
//    printLog(List((s"Precursor map (${precursors.size})", Console.YELLOW)))
    printLog(List((s"Memo (${memo.size})", Console.YELLOW)))
    stats.updateMaxWLSize(sz)

    worklist match {
      case Nil => // No more goals to try: synthesis failed
        None
      case node :: rest => {
        stats.addExpandedGoal(node)
        val res = memo.lookup(node.goal) match {
          case Some(Failed()) => {
            printLog(List((s"Recalled FAIL", RED)))
            Left(node.fail(rest))
          }
          case Some(Succeeded(sol)) => {
            printLog(List((s"Recalled solution ${sol._1}", RED)))
            node.succeed(sol, rest)
          }
          case None => expandNode(node, rest)
        }
        res match {
          case Left(newWorklist) => processWorkList(newWorklist)
          case Right(solution) => Some(solution)
        }
      }
    }
  }

  protected def expandNode(node: OrNode, rest: List[OrNode])(implicit stats: SynStats,
                                         config: SynConfig): Either[List[OrNode], Solution] = {
    val goal = node.goal
    implicit val ind = goal.depth
    if (config.printEnv) {
      printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
    }
    printLog(List((s"${goal.pp}", Console.BLUE)))

    // Apply all possible rules to the current goal to get a list of alternative expansions,
    // each of which can have multiple open subgoals
    val rules = nextRules(node)
    val expansions =
      if (goal.isUnsolvable) Nil  // This is a special unsolvable goal, discard eagerly
      else applyRules(rules)(node, stats, config, ind)

    // Check if any of the expansions is a terminal
    expansions.find(_.subgoals.isEmpty) match {
      case Some(e) => node.succeed(e.kont(Nil), rest)
      case None => { // no terminals: add all expansions to worklist
        val newNodes = for {
          (e, i) <- expansions.zipWithIndex
          //              alternatives = expansions.filter(_.rule == e.rule)
          //              altLabel = if (alternatives.size == 1) "" else alternatives.indexOf(e).toString // this is here only for logging
          andNode = AndNode(i +: node.id, e.kont, node, e.consume, e.rule)
          nSubs = e.subgoals.size
          (g, j) <- if (nSubs == 1) List((e.subgoals.head, -1)) // this is here only for logging
          else e.subgoals.zip(Range(nSubs - 1, -1, -1))
          produce = g.allHeaplets - (goal.allHeaplets - e.consume)
        } yield OrNode(j +: andNode.id, g, Some(andNode), produce)

        def isSubsumed(n: OrNode): Boolean = {
          precursors.subsumer(n, node) match {
            case None => false
            case Some(s) => {
              printLog(List((s"Application ${n.pp()} commutes with earlier ${s.pp()}", RED)))
              true
            }
          }
        }

        for {
          n <- newNodes.filter(n => isSubsumed(n))
        } stats.filteredNodes += n

        val filteredNodes = newNodes
        for ((n, i) <- newNodes.zipWithIndex) {

          val precs = newNodes.take(i).map(_.transition).toSet
          if (filteredNodes.contains(n))
          // If this node has younger and-siblings, do not add any precursors:
          // the precursor might have failed because of its younger sibling
          // and not because of n!
            precursors.save(n.id, precs)
        }

        if (filteredNodes.isEmpty) {
          // This is a dead-end: prune worklist and try something else
          printLog(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
          Left(node.fail(rest))
        } else {
          stats.addGeneratedGoals(filteredNodes.size)
          Left(filteredNodes.toList ++ rest)
        }
      }
    }
  }


  protected def applyRules(rules: List[SynthesisRule])(implicit node: OrNode,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ind: Int): Seq[RuleResult] = {
    implicit val goal = node.goal
    implicit val ind = goal.depth
    rules match {
      case Nil => Vector() // No more rules to apply: done expanding the goal
      case r :: rs =>
        // Invoke the rule
        val children = r(goal)

        if (children.isEmpty) {
          // Rule not applicable: try other rules
          printLog(List((s"$r FAIL", BLACK)), isFail = true)
          applyRules(rs)
        } else {
          // Rule applicable: try all possible sub-derivations
          val childFootprints = children.map(c => s"$GREEN{${c.consume.pre.pp}}$MAGENTA{${c.consume.post.pp}}$BLACK")
          printLog(List((s"$r (${children.size}): ${childFootprints.head}", BLACK)))
          for {c <- childFootprints.tail}
            printLog(List((c, BLACK)))(config = config, ind = goal.depth + 1)

          if (config.invert && r.isInstanceOf[InvertibleRule]) {
            // The rule is invertible: do not try other rules on this goal
            children
          } else {
            // Both this and other rules apply
            children ++ applyRules(rs)
          }
        }
    }
  }

  private def getIndent(implicit ind: Int): String = if (ind <= 0) "" else "|  " * ind

  protected def printLog(sc: List[(String, String)], isFail: Boolean = false)
                      (implicit config: SynConfig, ind: Int = 0): Unit = {
    if (config.printDerivations) {
      if (!isFail || config.printFailed) {
        for ((s, c) <- sc if s.trim.length > 0) {
          print(s"$BLACK$getIndent")
          println(s"$c${s.replaceAll("\n", s"\n$BLACK$getIndent$c")}")
        }
      }
      print(s"$BLACK")
    }
  }

}