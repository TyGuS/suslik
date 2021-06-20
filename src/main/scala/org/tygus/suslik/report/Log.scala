package org.tygus.suslik.report

import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis.rules.Rules.RuleResult
import org.tygus.suslik.util.SynLogging

import scala.Console.{GREEN, MAGENTA, RESET}

class Log(val out: SynLogging) {
  import Log.Context

  def showChildren(goal: Goal)(c: RuleResult): String = {
    def showFootprint(f: Footprint): String = s"$GREEN${f.pre.pp}$MAGENTA${f.post.pp}$RESET"
    def showDiff(subgoal: Goal):String = s"${showFootprint(goal.toFootprint - subgoal.toFootprint)} --> ${showFootprint(subgoal.toFootprint - goal.toFootprint)}"

    c.subgoals.length match {
      case 0 => showFootprint(goal.toFootprint)
      case _ => c.subgoals.map(showDiff).mkString("; ") // ++ s"$CYAN[${c.transitions.map(_.pp).mkString("; ")}]$RESET"
    }
  }

  private def getIndent(ind: Int): String = if (ind <= 0) "" else "|  " * ind

  private def getIndent(implicit ctx: Context): String = ctx.goal match {
    case None => ""
    case Some(goal) => getIndent(goal.depth)
  }

  def print(msg: String, color: String, level: Int = 1)
                        (implicit config: SynConfig, ctx: Context = Context()): Unit = {
    if (config.traceLevel >= level) {
      out.print(s"$RESET$getIndent")
      out.println(s"$color${msg.replaceAll("\n", s"\n$RESET$getIndent$color")}")
      out.print(s"$RESET")
    }
  }
}

object Log {

  case class Context(goal: Option[Goal] = None)
  object Context {
    def apply(goal: Goal): Context = Context(Some(goal))
  }
}

