package org.tygus.suslik.util

import org.tygus.suslik.language.Statements
import org.tygus.suslik.language.Statements.{Procedure, Statement}
import org.tygus.suslik.logic.FunSpec
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.report.StopWatch
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.{Memoization, SynConfig}

import scala.collection.mutable
import scala.concurrent.duration._
import scala.io.StdIn

/**
  * @author Ilya Sergey
  */

sealed abstract class SynLogging {
  def print(s: String): Unit

  def println(s: String): Unit

  def println(): Unit

  def printlnErr(s: String): Unit

  def testPrintln(s: String, color: String = Console.RESET): Unit

  def readInt: Int
}

/**
  * Different loggind levels
  */
object SynLogLevels {

  object Verbose extends SynLogging {
    override def printlnErr(s: String): Unit = System.err.println(s)

    override def print(s: String): Unit = Console.print(s)

    override def println(s: String): Unit = Console.println(s)

    override def testPrintln(s: String, color: String = Console.RESET): Unit = {
      Console.println(s"$color$s${Console.RESET}")
    }

    override def println(): Unit = Console.println()

    def readInt: Int = StdIn.readInt()
  }

  object Test extends SynLogging {
    // Mute standard print
    override def println(s: String): Unit = {}

    override def print(s: String): Unit = {}

    override def println(): Unit = {}

    override def printlnErr(s: String): Unit = Console.println(s)

    override def testPrintln(s: String, color: String = Console.RESET): Unit = {
      Console.println(s"$color$s${Console.RESET}")
    }

    def readInt: Int = 0
  }

}

case class RuleStat(numSuccess: Int, timeSuccess: Long, numFail: Int, timeFail: Long)

class SynStats(timeOut: Long) {
  // When did the synthesis start?
  private var startTime: Deadline = Deadline.now
  // Total number of goals generated
  private var goalsGenerated: Int = 1
  // Total number of goals to which rules were applied
  private var goalsExpanded: Int = 0
  // Maximum goal depth
  private var maxDepth: Int = 0
  // Maximum size of the worklist
  private var maxWLSize: Int = 0
  // For each explored search node: how many of its (reflexive) descendants have been explored?
  private val descendantsExplored: mutable.Map[NodeId, Int] = mutable.Map()
  // Nodes that have been backtracked out of
  private val failedNodes: mutable.HashSet[AndNode] = mutable.HashSet()
  // Which rules were applied how many times and how long they took
  private val ruleApplications: mutable.Map[String, RuleStat] = mutable.Map()
  // Rule applications picked interactively
  private var expansionChoices: List[Int] = List()
  // Time spent in SMT
  private var smtTime: Long = 0
  // Time spent in Cyclist
  private var cyclistTime: Long = 0

  // Have we reached the timeout yet?
  def timedOut: Boolean = (startTime + timeOut.milliseconds).isOverdue()
  // How long has passed since synthesis started
  def duration: Long = (Deadline.now - startTime).toMillis
  // Start recording time
  def start(): Unit = { startTime = Deadline.now }

  // Tell all n's ancestors that n has been explored
  private def markExplored(n: OrNode): Unit = {
    descendantsExplored.put(n.id, descendantsExplored.getOrElse(n.id, 0) + 1)
    n.parent match {
      case None =>
      case Some(an) =>
        descendantsExplored.put(an.id, descendantsExplored.getOrElse(an.id, 0) + 1)
        markExplored(an.parent)
    }
  }

  // Record that n has failed
  def addFailedNode(n: AndNode): Unit = {
    failedNodes.add(n)
  }

  def addGeneratedGoals(n: Int): Unit = {
    goalsGenerated = goalsGenerated + n
  }

  def addExpandedGoal(n: OrNode): Unit = {
    goalsExpanded = goalsExpanded + 1
    maxDepth = maxDepth.max(n.depth)
    markExplored(n)
  }

  def addExpansionChoice(choice: Int): Unit =
    expansionChoices = expansionChoices ++ List(choice)

  def updateMaxWLSize(sz: Int): Unit = {
    maxWLSize = maxWLSize.max(sz)
  }

  def hotNodes(count: Int = 1): List[(AndNode, Int)] = {
    val maxNodes = failedNodes.toList.sortBy(n => -descendantsExplored(n.id)).take(count)
    maxNodes.map(n => (n, descendantsExplored(n.id)))
  }
  
  def recordSMTTime[T](op: => T): T = {
    val (result, time) = StopWatch.timed(op)
    smtTime += time
    result
  }

  def recordCyclistTime[T](op: => T): T = {
    val (result, time) = StopWatch.timed(op)
    cyclistTime += time
    result
  }

  def recordRuleApplication[T](name: String, op: => Seq[T]): Seq[T] = {
    val (result, time) = StopWatch.timed(op)
    val oldStat = ruleApplications.getOrElse(name, RuleStat(0,0,0,0))
    if (result.isEmpty)
      ruleApplications.update(name, oldStat.copy(numFail = oldStat.numFail + 1, timeFail = oldStat.timeFail + time))
    else
      ruleApplications.update(name, oldStat.copy(numSuccess = oldStat.numSuccess + 1, timeSuccess = oldStat.timeSuccess + time))
    result
  }

  def expensiveRules(count: Int = 5): List[(String, RuleStat)] = {
    ruleApplications.toList.sortBy{ case (_, stat) => -stat.timeSuccess - stat.timeFail }.take(count)
  }
  
  def numGoalsGenerated: Int = goalsGenerated
  def numGoalsExpanded: Int = goalsExpanded
  def numGoalsFailed: Int = failedNodes.size
  def numRulesApplied: Int = ruleApplications.map( x => x._2.numSuccess).sum
  def maxWorklistSize: Int = maxWLSize
  def maxGoalDepth: Int = maxDepth
  def smtCacheSize: Int = SMTSolving.cacheSize
  def memoSize: (Int, Int, Int) = Memoization.memo.size
  def getExpansionChoices: List[Int] = expansionChoices
  def timeCycling: Long = cyclistTime
}

// TODO: refactor me to make more customizable
object SynStatUtil {

  import java.io.{File, FileWriter}

  val myStats = "stats.csv"
  val myFile = new File(myStats)
  val initRow: String =
    List("Name", "Time", "Spec Size", "Num Procs", "Code Size", "Backtrackings", "Applications", "Num Statements", "Goals generated", "Rules applied", "Max Worklist Size", "SMT Cache").mkString(", ") + "\n"

  def init(config: SynConfig){
    if (config.logToFile) {
      if (myFile.exists()) myFile.delete()
      myFile.createNewFile()
      using(new FileWriter(myFile, true))(_.write(initRow))
    }
  }

  def using[A <: {def close() : Unit}, B](resource: A)(f: A => B): B =
      try f(resource) finally resource.close()

  def countStmts(proc: Procedure): Int = {
    def countInner(s: Statement): Int = s match {
      case Statements.Skip => 0
      //case Statements.Hole =>
      case Statements.Error => 1
      case Statements.Malloc(to, tpe, sz) => 1
      case Statements.Free(_) => 1
      case Statements.Load(_,_,_,_) => 1
      case Statements.Store(_,_,_) => 1
      case Statements.Call(_,_,_) => 1
      case Statements.SeqComp(s1, s2) => countInner(s1) + countInner(s2)
      case Statements.If(_, tb, eb) => 1 + countInner(tb) + countInner(eb)
      case Statements.Guarded(_, body) => 1 + countInner(body)
    }
    countInner(proc.body)
  }

  def log(name: String, time: Long, config: SynConfig, spec: FunSpec, res: List[Procedure], stats: SynStats): Unit = {
    if (config.logToFile) {
      val statRow = (res match {
        case Nil => List("FAIL", "FAIL", "FAIL", stats.numGoalsGenerated, stats.numRulesApplied, stats.maxWorklistSize)
        case procs => List(procs.length, procs.map(_.body.size).sum, procs.map(countStmts).sum, stats.numGoalsGenerated, stats.numRulesApplied, stats.maxWorklistSize)
      }).mkString(", ")

      val specSize = spec.pre.size + spec.post.size
      val data = s"$name, $time, $specSize, $statRow, ${config.pp}\n"
      using(new FileWriter(myFile, true))(_.write(data))
    }
  }

}