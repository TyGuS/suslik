package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.util.{SynLogging, SynStats}
import org.tygus.suslik.synthesis.rules.Rules._

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
    val FunSpec(name, tp, formals, pre, post) = funGoal
    val goal = topLevelGoal(pre, post, formals, name, env)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))(i = 0, config)
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
                          (stats: SynStats)
                          (implicit ind: Int = 0): Option[Solution] = {
    // Initialize worktree: root or-node containing the top-level goal
    val worktree = OrNode("", goal, Nil) // Vector(RuleResult(List(goal), idProducer("init")))
    worktree.process(stats, goal.env.config, ind)
  }

  case class OrNode(label: String, goal: Goal, children: Seq[AndNode], parent: Option[AndNode] = None) {

    @tailrec final def process(implicit
                stats: SynStats,
                config: SynConfig,
                ind: Int): Option[Solution] = children match {
        case c +: rest => c.copy(parent = Some(this.copy(children = rest))).process // This is an internal node: recurse
        case Nil => { // this is a leaf: expand
          printLog(List((s"Goal to expand: ${goal.label.pp} (depth: ${goal.depth})", Console.BLUE)))
          stats.updateMaxDepth(goal.depth)
          if (config.printEnv) {
            printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
          }
          printLog(List((s"${goal.pp}", Console.BLUE)))

          // Apply all possible rules to the current goal to get a list of alternatives,
          // each of which can have multiple open goals
          val rules = nextRules(goal, 0)
          val results =
            if (goal.isUnsolvable) Nil  // This is a special unsolvable goal, discard eagerly
            else applyRules(rules)(goal, stats, config, ind)

          if (results.isEmpty) { // This is a dead-end: backtrack
            stats.bumpUpBacktracing()
            printLog(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
            fail match { // Check if there are unexplored alternatives left
              case None => None           // No: synthesis fails
              case Some(p) => p.process   // Yes: process the next alternative
            }
          } else { // Goal has been expanded: grow the search tree
            val newChildren = results.zipWithIndex.map { case (res, i) => AndNode(i.toString + label,  res.kont,
              res.subgoals.zipWithIndex.map{case (g, j) => OrNode(j.toString + i.toString + label, g, Nil)})}
            copy(children = newChildren).process
          }
        }
      }

    def fail: Option[OrNode] = parent match {
      case Some(p) => p.fail
      case None => None
    }

    def succeed(s: Solution): Either[AndNode, Solution] = parent match {
      case None => Right(s)
      case Some(p) => {
        if (p.children.isEmpty) {
          p.succeed(p.kont(List(s)))
        } else {
          Left(p.copy(kont = p.kont.partApply(s)))
        }
      }
    }
  }

  case class AndNode(label: String, kont: StmtProducer, children: Seq[OrNode], parent: Option[OrNode] = None) {
    @tailrec final def process(implicit
                stats: SynStats,
                config: SynConfig,
                ind: Int): Option[Solution] = children match {
        case c +: rest => c.copy(parent = Some(this.copy(children = rest))).process // This is an internal node: recurse // There are open subgoals, so solve the first one
        case Nil => succeed(kont(Nil)) match { // No open subgoals: synthesis of this an-node suceeds
          case Left(n) => n.process
          case Right(sol) => Some(sol)
        }
      }

    // TODO: also handle case where this is not the first child
    def fail: Option[OrNode] = parent match {
      case Some(p) => {
        if (p.children.isEmpty) {
          // This was the last alternative: delete parent too
          p.fail
        } else {
          // Parent has other alternatives: just delete me
          Some(p)
        }
      }
      case None =>
        assert(false, "Found active and-node with an empty parent")
        None
    }

    def succeed(s: Solution): Either[AndNode, Solution] = parent match {
      case Some(p) => p.succeed(s)
      case None =>
        assert(false, "Found active and-node with an empty parent")
        Left(this)
    }
  }


//  @tailrec
//  private def processWorkList(worktree: OrNode)
//                             (implicit
//                              stats: SynStats,
//                              config: SynConfig,
//                              ind: Int): Option[Solution] = {
//
//    // Check for timeouts
//    val currentTime = System.currentTimeMillis()
//    if (currentTime - config.startTime > config.timeOut) {
//      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut.toDouble / 1000} seconds.\n")
//    }
//
//    val sz = worklist.length
//    printLog(List((s"\nWorklist ($sz): ${worklist.map(_.pp).mkString(" ")}", Console.YELLOW)))
//    stats.updateMaxWLSize(sz)
//
//    worklist match {
//      case Nil =>
//        // No more subderivations to try: synthesis failed
//        None
//      case subderiv +: rest => subderiv.subgoals match {
//        // Otherwise pick a subderivation to expand
//        case Nil =>
//          // This subderivation has no open goals: synthesis succeeded, build the solution
//          Some(subderiv.kont(Nil))
//        case goal :: moreGoals => {
//          // Otherwise, expand the first open goal
//          printLog(List((s"Goal to expand: ${goal.label.pp} (depth: ${goal.depth})", Console.BLUE)))
//          stats.updateMaxDepth(goal.depth)
//          if (config.printEnv) {
//            printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
//          }
//          printLog(List((s"${goal.pp}", Console.BLUE)))
//
//          // Apply all possible rules to the current goal to get a list of alternatives,
//          // each of which can have multiple open goals
//          val rules = nextRules(goal, 0)
//          val children =
//            if (goal.isUnsolvable) Nil  // This is a special unsolvable goal, discard eagerly
//            else applyRules(rules)(goal, stats, config, ind)
//
//          if (children.isEmpty) {
//            stats.bumpUpBacktracing()
//            printLog(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
//          }
//
//          val newSubderivations = children.map(child => {
//            // To turn a child into a valid subderivation,
//            // add the rest of the open goals from the current subderivation,
//            // and set up the solution producer to join results from all the open goals
//            RuleResult(child.subgoals ++ moreGoals, child.kont >> subderiv.kont)
//          })
//          // Add new subderivations to the worklist, sort by cost and process
//          val newWorkList = newSubderivations ++ rest
////          val newWorkList = if (config.depthFirst) newWorkList_ else newWorkList_.sortBy(_.cost)
//          processWorkList(newWorkList)
//        }
//      }
//    }
//  }

  protected def applyRules(rules: List[SynthesisRule])(implicit goal: Goal,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ind: Int): Seq[RuleResult] = rules match
  {
    case Nil => Vector() // No more rules to apply: done expanding the goal
    case r :: rs =>
      val goalStr = s"$r: "
      // Invoke the rule
      val allChildren = r(goal)
      // Filter out children that contain out-of-order goals
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
        val succ = s"SUCCESS, ${children.size} alternative(s): ${children.map(_.pp).mkString(", ")}"
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

  // Is current goal supposed to appear before g?
  def goalOutOfOrder(g: Goal)(implicit goal: Goal,
                              stats: SynStats,
                              config: SynConfig,
                              ind: Int): Boolean = {
    g.hist.outOfOrder(allRules(goal)) match {
      case None => false
      case Some(app) =>
        //              printLog(List((g.deriv.preIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        //              printLog(List((g.deriv.postIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        printLog(List((s"${RED}Alternative ${g.hist.applications.head.pp} commutes with earlier ${app.pp}", BLACK)))
        true
    }
  }

  private def getIndent(implicit i: Int): String = if (i <= 0) "" else "|  " * i

  protected def printLog(sc: List[(String, String)], isFail: Boolean = false)
                      (implicit i: Int, config: SynConfig): Unit = {
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