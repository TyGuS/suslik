package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.SearchTree._
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.util.{SynLogging, SynStats}

import scala.Console._
import scala.annotation.tailrec

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis extends SepLogicUtils {

  val log: SynLogging

  import log._

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)


  def allRules(goal: Goal): List[SynthesisRule]

  def nextRules(goal: Goal, depth: Int): List[SynthesisRule]

  def synthesizeProc(funGoal: FunSpec, env: Environment): Option[(List[Procedure], SynStats)] = {
    implicit val config: SynConfig = env.config
    // Cleanup the memo table
    val FunSpec(name, tp, formals, pre, post) = funGoal
    val goal = topLevelGoal(pre, post, formals, name, env)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))
    val stats = new SynStats()
    SMTSolving.init()
    try {
      synthesize(goal)(stats = stats) match {
        case Some((body, helpers)) =>
          val main = Procedure(name, tp, formals, body)
          Some(main :: helpers, stats)
        case None =>
          printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp}")
          None
      }
    } catch {
      case SynTimeOutException(msg) =>
        printlnErr(msg)
        None
    }
  }

  protected def synthesize(goal: Goal)
                          (stats: SynStats): Option[Solution] = {
    // Initialize worklist: root or-node containing the top-level goal
    val worklist = List(OrNode(Vector(), goal, None))
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
    val workListLog = s"Worklist ($sz): ${worklist.map(_.pp()).mkString(" ")}"
    printLog(List((workListLog, Console.YELLOW)))
    stats.updateMaxWLSize(sz)

    worklist match {
      case Nil => // No more goals to try: synthesis failed
        None
      case node :: rest => {
        val goal = node.goal
        implicit val ind = goal.depth
        stats.updateMaxDepth(goal.depth)
        if (config.printEnv) {
          printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
        }
        printLog(List((s"${goal.pp}", Console.BLUE)))

        // Apply all possible rules to the current goal to get a list of alternative expansions,
        // each of which can have multiple open subgoals
        val rules = nextRules(goal, 0)
        val expansions =
          if (goal.isUnsolvable) Nil // This is a special unsolvable goal, discard eagerly
          else applyRules(rules)(goal, stats, config, ind)

        if (expansions.isEmpty) {
          // This is a dead-end: prune worklist and try something else
          stats.bumpUpBacktracing()
          printLog(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
          processWorkList(node.fail(rest))
        } else {
          // Check if any of the expansions is a terminal
          expansions.find(_.subgoals.isEmpty) match {
            case Some(e) => node.succeed(e.kont(Nil), rest) match { // e is a terminal: this node suceeded
              case Right(sol) => Some(sol) // No more open subgoals in this derivation: synthesis suceeded
              case Left(newWorkList) => processWorkList(newWorkList) // More open goals: continue
            }
            case None => { // no terminals: add all expansions to worklist
              val newNodes = for {
                (e, i) <- expansions.zipWithIndex
                alternatives = expansions.filter(_.label == e.label)
                altLabel = if (alternatives.size == 1) "" else alternatives.indexOf(e).toString // this is here only for logging
                andNode = AndNode(i +: node.id, e.kont, node, e.label ++ altLabel)
                (g, j) <- if (e.subgoals.size == 1) List((e.subgoals.head, -1)) // this is here only for logging
                            else e.subgoals.zipWithIndex
              } yield OrNode(j +: andNode.id, g, Some(andNode))
              processWorkList(newNodes.toList ++ rest)
            }
          }
        }
      }
    }
  }

  protected def applyRules(rules: List[SynthesisRule])(implicit goal: Goal,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ind: Int): Seq[RuleResult] = {
    implicit val ind = goal.depth
    rules match {
      case Nil => Vector() // No more rules to apply: done expanding the goal
      case r :: rs =>
        val goalStr = s"$r: "
        // Invoke the rule
        val allChildren = r(goal)
        // Filter out children that contain out-of-order goals
        
        // TODO [Commute]: This is a commute optimisation that affects completeness 
        val children = if (config.commute) {
          allChildren.filterNot(_.subgoals.exists(goalOutOfOrder))
        } else allChildren

        if (children.isEmpty) {
          // Rule not applicable: try other rules
          printLog(List((s"${goalStr}FAIL", BLACK)), isFail = true)
          applyRules(rs)
        } else {
          // Rule applicable: try all possible sub-derivations
          //        val subSizes = children.map(c => s"${c.subgoals.size} sub-goal(s)").mkString(", ")
          val succ = s"SUCCESS, ${children.size} alternative(s)" // TODO: print consume set?
          printLog(List((s"$goalStr$GREEN$succ", BLACK)))
          stats.bumpUpRuleApps()
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

  // Is current goal supposed to appear before g?
  def goalOutOfOrder(g: Goal)(implicit goal: Goal,
                              stats: SynStats,
                              config: SynConfig): Boolean = {
    implicit val ind = goal.depth
    g.hist.outOfOrder(allRules(goal)) match {
      case None => false
      case Some(app) =>
        //              printLog(List((g.deriv.preIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        //              printLog(List((g.deriv.postIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        printLog(List((s"${RED}Alternative ${g.hist.applications.head.pp} commutes with earlier ${app.pp}", BLACK)))
        true
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