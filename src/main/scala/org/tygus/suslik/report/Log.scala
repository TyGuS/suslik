package org.tygus.suslik.report

import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis.rules.Rules.RuleResult
import org.tygus.suslik.util.SynLogging

import scala.Console.{GREEN, MAGENTA, RESET}

class Log(val out: SynLogging) {

  case class Context(goal: Option[Goal] = None)

  object Context{
    def apply(goal: Goal): Context = Context(Some(goal))
  }

  def showChild(goal: Goal)(c: RuleResult): String = {
    def showFootprint(f: Footprint): String = s"$GREEN${f.pre.pp}$MAGENTA${f.post.pp}$RESET"
    def showTransition(subgoal: Goal):String = s"${showFootprint(goal.toFootprint - subgoal.toFootprint)} --> ${showFootprint(subgoal.toFootprint - goal.toFootprint)}"

    c.subgoals.length match {
      case 0 => showFootprint(goal.toFootprint)
      case _ => c.subgoals.map(showTransition).mkString(", ")
    }
  }

  private def getIndent(ind: Int): String = if (ind <= 0) "" else "|  " * ind

  private def getIndent(implicit ctx: Context): String = ctx.goal match {
    case None => ""
    case Some(goal) => getIndent(goal.depth)
  }

  def print(sc: List[(String, String)], isFail: Boolean = false)
                        (implicit config: SynConfig, ctx: Context = Context()): Unit = {
    if (config.printDerivations) {
      if (!isFail || config.printFailed) {
        for ((s, c) <- sc if s.trim.length > 0) {
          out.print(s"$RESET$getIndent")
          out.println(s"$c${s.replaceAll("\n", s"\n$RESET$getIndent$c")}")
        }
      }
      out.print(s"$RESET")
    }
  }

}

