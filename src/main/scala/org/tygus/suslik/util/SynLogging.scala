package org.tygus.suslik.util

import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.FunSpec
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.SynConfig
import scalaz.DList
import scala.collection.mutable

/**
  * @author Ilya Sergey
  */

sealed abstract class SynLogging {
  def print(s: String): Unit

  def println(s: String): Unit

  def println(): Unit

  def printlnErr(s: String): Unit

  def testPrintln(s: String, color: String = Console.BLACK): Unit
}

/**
  * Different loggind levels
  */
object SynLogLevels {

  object Verbose extends SynLogging {
    override def printlnErr(s: String): Unit = System.err.println(s)

    override def print(s: String): Unit = Console.print(s)

    override def println(s: String): Unit = Console.println(s)

    override def testPrintln(s: String, color: String = Console.BLACK): Unit = {
      Console.println(s"$color$s${Console.BLACK}")
    }

    override def println(): Unit = Console.println()
  }

  object Test extends SynLogging {
    // Mute standard print
    override def println(s: String): Unit = {}

    override def print(s: String): Unit = {}

    override def println(): Unit = {}

    override def printlnErr(s: String): Unit = Console.println(s)

    override def testPrintln(s: String, color: String = Console.BLACK): Unit = {
      Console.println(s"$color$s${Console.BLACK}")
    }
  }

}

class SynStats {
  // Total number of goals generated
  private var goalsGenerated: Int = 0
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

  def updateMaxWLSize(sz: Int): Unit = {
    maxWLSize = maxWLSize.max(sz)
  }

  def hotNodes(count: Int = 1): List[(AndNode, Int)] = {
    val maxNodes = failedNodes.toList.sortBy(n => -descendantsExplored(n.id)).take(count)
    maxNodes.map(n => (n, descendantsExplored(n.id)))
  }
  def numGoalsGenerated: Int = goalsGenerated
  def numGoalsExpanded: Int = goalsExpanded
  def numGoalsFailed: Int = failedNodes.size
  def maxWorklistSize: Int = maxWLSize
  def maxGoalDepth: Int = maxDepth
  def smtCacheSize: Int = SMTSolving.cacheSize
}

// TODO: refactor me to make more customizable
object SynStatUtil {

  import java.io.{File, FileWriter}

  val myStats = "stats.csv"
  val myFile = new File(myStats)
  val initRow: String =
    List("Name", "Time", "Spec Size", "Code Size", "Backtrackings", "Applications", "Max Worklist Size", "SMT Cache").mkString(", ") + "\n"

  def init(config: SynConfig){
    if (config.logToFile) {
      if (myFile.exists()) myFile.delete()
      myFile.createNewFile()
      using(new FileWriter(myFile, true))(_.write(initRow))
    }
  }

  def using[A <: {def close() : Unit}, B](resource: A)(f: A => B): B =
      try f(resource) finally resource.close()

  def log(name: String, time: Long, config: SynConfig, spec: FunSpec, stats: Option[(List[Procedure], SynStats)]): Unit = {
    if (config.logToFile) {
      val statRow = (stats match {
        case Some((procs, st)) => List(procs.map(_.body.size).sum, st.numGoalsFailed, st.numGoalsGenerated, st.maxWorklistSize, st.smtCacheSize)
        case None => DList.replicate(5, "FAIL").toList
      }).mkString(", ")

      val specSize = spec.pre.size + spec.post.size
      val data = s"$name, $time, $specSize, $statRow, ${config.pp}\n"
      using(new FileWriter(myFile, true))(_.write(data))
    }
  }

}