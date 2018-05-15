package org.tygus.synsl.synthesis

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._
import org.tygus.synsl.synthesis.rules.InvertibleRule
import org.tygus.synsl.util.SynLogging

import scala.Console.{BLACK, BLUE, CYAN, GREEN, MAGENTA, RED, YELLOW}
import scala.collection.mutable.ListBuffer

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis {

  val log: SynLogging

  import log._

  val synQualifier: String = "synthesis"

  case class SynthesisException(msg: String) extends SynSLException(synQualifier, msg)

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  val rulesToApply: List[SynthesisRule]
  val maxDepth: Int

  def synthesizeProc(funGoal: FunSpec, env: Environment, _printFails: Boolean = true): Option[Procedure] = {
    val FunSpec(name, tp, formals, pre, post) = funGoal
    val goal = Goal(pre, post, formals, name)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))(0)
    synthesize(goal, env, maxDepth)(printFails = _printFails) match {
      case Some(body) => Some(Procedure(name, tp, goal.gamma, body))
      case None =>
        printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp},\n depth = $maxDepth.")
        None
    }

  }

  private def synthesize(goal: Goal, env: Environment, maxDepth: Int = 25)
                        (implicit ind: Int = 0, printFails: Boolean): Option[Statement] = {

    printLog(List((s"${env.pp}", Console.MAGENTA)))
    printLog(List((s"${goal.pp}", Console.BLUE)))

    if (maxDepth < 0) return None

    def tryRules(rules: List[SynthesisRule]): Option[Statement] = rules match {
      case Nil => None
      case r :: rs =>

        // Try alternative sub-derivations after applying `r`
        def tryAlternatives(alts: Seq[Subderivation], altIndex: Int): Option[Statement] = alts match {
          case (a :: as) =>
            if (altIndex > 0) printLog(List((s"${r.toString} Trying alternative sub-derivation $altIndex:", MAGENTA)))
            solveSubgoals(a) match {
              case Some(res) => Some(res) // This alternative succeeded
              case None => tryAlternatives(as, altIndex + 1) // This alternative failed: try other alternatives
            }
          case Nil =>
            // All alternatives have failed
            if (r.isInstanceOf[InvertibleRule]) {
              // Do not backtrack application of this rule: the rule is invertible and cannot be the reason for failure
              printLog(List((s"${r.toString} All sub-derivations failed: invertible rule, do not backtrack.", MAGENTA)))
              None
            } else {
              // Backtrack application of this rule
              printLog(List((s"${r.toString} All sub-derivations failed: backtrack.", MAGENTA)))
              tryRules(rs)
            }
        }

        // Solve all sub-goals in a sub-derivation
        def solveSubgoals(s: Subderivation): Option[Statement] = {

          // Optimization: if one of the subgoals failed, to not try the rest!
          // <ugly-imperative-code>
          val results = new ListBuffer[Option[Statement]]
          import util.control.Breaks._
          breakable {
            for {(subgoal, subenv) <- s.subgoals} {
              synthesize(subgoal, subenv, maxDepth - 1)(ind + 1, printFails) match {
                case s@Some(_) => results.append(s)
                case _ => break
              }
            }
          }
          // </ugly-imperative-code>

          val resultStmts = for (r <- results if r.isDefined) yield r.get
          if (resultStmts.size < s.subgoals.size) {
            // One of the sub-goals failed: this sub-derivation fails
            None
          } else {
            Some(s.kont(resultStmts))
          }
        }

        val subderivations = r(goal, env)
        val goalStr = s"$r: "
        if (subderivations.isEmpty) {
          // Rule not applicable: try the rest
          printLog(List((s"$goalStr${RED}FAIL", BLACK)), isFail = true)
          tryRules(rs)
        } else {
          // Rule applicable: try all possible sub-derivations
          val subSizes = subderivations.map(s => s"${s.subgoals.size} sub-goal(s)").mkString(", ")
          val succ = s"SUCCESS at depth $ind, ${subderivations.size} alternative(s) [$subSizes]"
          printLog(List((s"$goalStr$GREEN$succ", BLACK)))
          tryAlternatives(subderivations, 0)
        }
    }

    tryRules(rulesToApply)
  }

  private def getIndent(implicit i: Int): String = if (i <= 0) "" else "|  " * i

  private def printLog(sc: List[(String, String)], isFail: Boolean = false)
                      (implicit i: Int, printFails: Boolean = true): Unit = {
    if (!isFail || printFails) {
      for ((s, c) <- sc if s.trim.length > 0) {
        print(s"$BLACK$getIndent")
        println(s"$c${s.replaceAll("\n", s"\n$BLACK$getIndent$c")}")
      }
    }
    print(s"$BLACK")
  }


}