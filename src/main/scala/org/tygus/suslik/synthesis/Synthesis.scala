package org.tygus.suslik.synthesis

import org.tygus.suslik.Memoization
import org.tygus.suslik.language.SSLType
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.{SApp, _}
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.rules.OperationalRules.{AllocRule, FreeRule, ReadRule, WriteRule}
import org.tygus.suslik.synthesis.rules.UnfoldingRules
import org.tygus.suslik.synthesis.rules.UnfoldingRules.CallRule
import org.tygus.suslik.util.OtherUtil.Accumulator
import org.tygus.suslik.util.{SynLogging, SynStats}

import scala.Console._
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis extends SepLogicUtils {

  val log: SynLogging

  import log._

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  def allRules(goal: Goal): List[SynthesisRule]

  val operationalRules: Set[SynthesisRule] = Set(
    AllocRule,
    FreeRule,
    WriteRule,
    ReadRule,
    CallRule
  )

  def entailmentCheckRules(goal: Goal): List[SynthesisRule] = {
    allRules(goal).filter(r => !operationalRules.contains(r) && r != UnfoldingRules.InductionRule) // Seems order matters
  }

  def nextRules(goal: Goal, depth: Int): List[SynthesisRule]

  val memo = new Memoization

  def cutHead(prog: Statement): (Statement, Option[Statement]) = prog match {
    case SeqComp(s1, s2) => {
      val (head, tail_first) = cutHead(s1)
      if (tail_first.isDefined) {
        (head, Some(SeqComp(tail_first.get, s2)))
      } else {
        (head, Some(s2))
      }
    }
    case other => (other, None)
  }

  // todo delete(?)
  def unrollSAppsWherePossible(initial_assertion: Assertion, goal:Goal):Assertion = {
    val sigma = initial_assertion.sigma
    val phi = initial_assertion.phi

    val sapp = sigma.chunks.find({case _:SApp => true case _ => false})
    if(sapp.isEmpty){
      initial_assertion
    }else{
      // borrowed from Open rule
      val SApp(pred, args, _) = sapp.get
      val remainingChunks = sigma.chunks.filter(_ != sapp.get)
      val env = goal.env
      assert(env.predicates.contains(pred), s"Undefined predicate: $pred")
      val InductivePredicate(_, params, clauses) = env.predicates(pred).refreshExistentials(goal.vars)
      val sbst = params.map(_._2).zip(args).toMap
      lazy val possible_unrollings = for{
        InductiveClause(_sel, _asn) <- clauses
        sel = _sel.subst(sbst)
        asn = _asn.subst(sbst)
        constraints = asn.phi
        body = asn.sigma
        if SMTSolving.valid(phi ==> sel)
        newPhi = phi && constraints
        _newSigma1 = SFormula(body.chunks).bumpUpSAppTags() // todo: what is bumpUpSAppTags for?
        _newSigma2 = SFormula(remainingChunks).lockSAppTags() // todo: what is lockSAppTags for?
        newSigma = SFormula(_newSigma1.chunks ++ _newSigma2.chunks)
      } yield Assertion(newPhi, newSigma)
      if(possible_unrollings.nonEmpty){
        unrollSAppsWherePossible(possible_unrollings.head, goal) // todo: is it finite?
      }else{
        initial_assertion
      }
    }
  }

  // Returns the goal after application of the statement
  // TODO: check every rule for soundness:
  //  1. Don't read ghosts,
  //  2. updates ProgramVars
  //  3. behaves according to paper
  //  4. Heaplet lookup isn't syntactic, but also looks for heaplets with another name, but same address wrt pure part
  //  5. Don't redefine
  def modifyPre(spec:Goal, statement:Statement):Goal = statement match {
    case Skip => spec
    case Hole => throw SynthesisException(Hole.pp + " is not allowed here")
    case Error => throw SynthesisException(Error.pp + " is not allowed here")
    case Magic => throw SynthesisException(Magic.pp + " is not allowed here")
    case cmd: Malloc => AllocRule.symbolicExecution(spec, cmd) // OK: 1, 2, 4, 5 Check: 3
    case cmd: Free => FreeRule.symbolicExecution(spec, cmd) // OK: 1,2,3,5 Wrong: 4
    case cmd: Store => WriteRule.symbolicExecution(spec, cmd) // OK: 1,2,3,4,5
    case cmd: Load => ReadRule.symbolicExecution(spec, cmd) // OK: 1,2,3,4,5
    case cmd: Call => CallRule.symbolicExecution(spec, cmd) // OK: 1, check: everything, because I dont understand its code
    case cmd: SubGoal => ??? // should be same as call with that signature
    case cmd: SeqComp => throw SynthesisException("Unexpected SeqComp")
    case cmd: If => throw SynthesisException("Found if-then-else in the middle of the program. if-then-else is currently allowed only in the end.")
    case Guarded(cond, _) => { // todo: why is it here?
      val newPhi = spec.pre.phi && cond
      val newPre = unrollSAppsWherePossible(Assertion(newPhi, spec.pre.sigma), spec)
      spec.copy(pre = newPre)
    }
  }


  // Propagates assertions from precondition to holes, converting them into subgoals
  // collects subgoals into synthesis_goals_acc
  // correctness_goals_acc collects goals, that must be completed without any code
  def propagatePre(spec: Goal,
                   funSketch: Statement,
                   synthesis_goals_acc: Accumulator[Goal],
                   correctness_goals_acc: Accumulator[Goal]): Statement =
    try {
      val (head, tail) = cutHead(funSketch)
      val new_head = head match {
        case Hole =>
          if (tail.isDefined) {
            throw SynthesisException("Found hole in the middle of the program. Holes are currently allowed only in the end.")
          }
          SubGoal(spec)
        case other => other
      }
      if (tail.isDefined) {
        val tail_spec: Goal = modifyPre(spec, head)
        val new_tail = propagatePre(tail_spec, tail.get, synthesis_goals_acc, correctness_goals_acc)
        SeqComp(new_head, new_tail)
      } else {
        new_head match {
          case sg@SubGoal(g) => {
            synthesis_goals_acc.put(g)
            sg
          }
          case If(cond, tb, eb) =>
            If(cond,
              propagatePre(modifyPre(spec, Guarded(cond, tb)), tb, synthesis_goals_acc, correctness_goals_acc),
              propagatePre(modifyPre(spec, Guarded(cond.not, eb)), eb, synthesis_goals_acc, correctness_goals_acc)
            )
          case other => {
            val correctness_goal: Goal = modifyPre(spec, head)
            correctness_goals_acc.put(correctness_goal)
            other
          }
        }
      }
    }
    catch {
      case SymbolicExecutionError(why) => {
        printlnErr(why)
        Error
      }
    }



// synthesizeProgramFromSketch
  def synthesizeProc(funGoal: FunSpec, env: Environment, funSketch:Statement):Option[(Procedure, SynStats)] ={
    implicit val config: SynConfig = env.config
    // Cleanup the memo table
    memo.cleanup()
    val FunSpec(name, tp, formals, pre, post, var_decl) = funGoal
    val initial_goal = makeNewGoal(pre, post, formals, name, env, var_decl)
    printLog(List(("Initial specification:", Console.BLACK), (s"${initial_goal.pp}\n", Console.BLUE)))(i = 0, config)

    val inductive_derivations = UnfoldingRules.InductionRule(initial_goal)
    val stats = new SynStats()
    SMTSolving.init()

    val subgoals = inductive_derivations.map({x => x.subgoals.head}) ++ List(initial_goal)
    val answers = subgoals.view
      .map({goal => synthesizeProcNoInduction(goal, env, funSketch, stats, tp, formals)})
      .collectFirst {case Some(x) => x}
    answers
  }

  def synthesizeProcNoInduction(goal:Goal, env: Environment, funSketch:Statement, stats:SynStats, tp:SSLType, formals:Formals):Option[(Procedure, SynStats)] = {
    implicit val config: SynConfig = env.config
    val subGoalsAcc = new Accumulator[Goal]()
    val corrGoalsAcc = new Accumulator[Goal]() // goals, where emp must be correct answer
    val specifiedBody = propagatePre(goal, funSketch.resolveOverloading(goal.gamma), subGoalsAcc, corrGoalsAcc)
    val subGoals = subGoalsAcc.get
    val correctness_goals = corrGoalsAcc.get

    println("Propagated synthesis goal:")
    println(specifiedBody.pp)

    if (specifiedBody == Error) {
      Some(Procedure(goal.fname, tp, formals, Error), stats)
    } else {
      try {
        for (corrGoal <- correctness_goals) {
          val solution =
            synthesize(corrGoal, config.startingDepth)(stats = stats, rules = entailmentCheckRules(corrGoal))
          if(!solution.contains(Skip) ){
            printlnErr(s"Correctness goal \n${corrGoal.pp} \nfailed: expected Skip, got:\n$solution")
            return Some(Procedure(goal.fname, tp, formals, Error), stats)
          }
        }
        var completeFunction: Option[Statement] = Some(specifiedBody)
        for (subGoal <- subGoals) {
          if (completeFunction.isDefined) {
            val solution = synthesize(subGoal, config.startingDepth)(stats = stats, rules = nextRules(subGoal, config.startingDepth+1))
            completeFunction = solution match {
              case Some(sol) => Some(completeFunction.get.replace(SubGoal(subGoal), sol))
              case _ =>
                printlnErr(s"Deductive synthesis failed for the subgoal\n ${subGoal.pp},\n depth = ${config.startingDepth}.")
                None
            }
          }
        }

        completeFunction match {
          case Some(body) =>
            val proc = Procedure(goal.fname, tp, formals, body)
            Some((proc, stats))
          case None =>
            printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp},\n depth = ${config.startingDepth}.")
            None
        }
      } catch {
        case SynTimeOutException(msg) =>
          printlnErr(msg)
          None
      }
    }
  }


  def synthesizeProc_old(funGoal: FunSpec, env: Environment):
  Option[(Procedure, SynStats)] = {
    implicit val config: SynConfig = env.config
    // Cleanup the memo table
    memo.cleanup()
    val FunSpec(name, tp, formals, pre, post, var_decl) = funGoal
    val goal = makeNewGoal(pre, post, formals, name, env, var_decl)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))(i = 0, config)
    val stats = new SynStats()
    SMTSolving.init()
    try {
      synthesize(goal, config.startingDepth)(stats = stats, rules = nextRules(goal, config.startingDepth)) match {
        case Some(body) =>
          val proc = Procedure(name, tp, formals, body)
          Some((proc, stats))
        case None =>
          printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp},\n depth = ${config.startingDepth}.")
          None
      }
    } catch {
      case SynTimeOutException(msg) =>
        printlnErr(msg)
        None
    }

  }

  private def synthesize(goal: Goal, depth: Int) // todo: add goal normalization
                        (stats: SynStats,
                         rules: List[SynthesisRule])
                        (implicit ind: Int = 0): Option[Statement] = {
    lazy val res: Option[Statement] = synthesizeInner(goal, depth)(stats, rules)(ind)
    memo.runWithMemo(goal, stats, rules, res)
  }

  private def synthesizeInner(goal: Goal, depth: Int)
                             (stats: SynStats,
                              rules: List[SynthesisRule])
                             (implicit ind: Int = 0): Option[Statement] = {
    implicit val config: SynConfig = goal.env.config

    if (config.printEnv) {
      printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
    }
    printLog(List((s"${goal.pp}", Console.BLUE)))

    val currentTime = System.currentTimeMillis()
    if (currentTime - goal.env.startTime > config.timeOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut.toDouble / 1000} seconds.\n")
    }

    if (depth < 0) {
      printLog(List(("Reached maximum depth.", RED)))
      return None
    }

    def tryRules(rules: List[SynthesisRule]): Option[Statement] = rules match {
      case Nil => None
      case r :: rs =>

        // Try alternative sub-derivations after applying `r`
        def tryAlternatives(alts: Seq[Subderivation], altIndex: Int): Option[Statement] = alts match {
          case Seq(a, as@_*) =>
            if (altIndex > 0) printLog(List((s"${r.toString} Trying alternative sub-derivation ${altIndex + 1}:", MAGENTA)))
            solveSubgoals(a) match {
              case Some(Magic) =>
                stats.bumpUpBacktracing()
                tryAlternatives(as, altIndex + 1) // This alternative is inconsistent: try other alternatives
              case Some(res) =>
                stats.bumpUpLastingSuccess()
                Some(res) // This alternative succeeded
              case None =>
                stats.bumpUpBacktracing()
                tryAlternatives(as, altIndex + 1) // This alternative failed: try other alternatives
            }
          case Seq() =>
            // All alternatives have failed
            if (config.invert && r.isInstanceOf[InvertibleRule]) {
              // Do not backtrack application of this rule: the rule is invertible and cannot be the reason for failure
              printLog(List((s"${r.toString} All sub-derivations failed: invertible rule, do not backtrack.", MAGENTA)))
              None
            } else {
              // Backtrack application of this rule
              stats.bumpUpBacktracing()
              printLog(List((s"${r.toString} All sub-derivations failed: backtrack.", MAGENTA)))
              tryRules(rs)
            }
        }

        // Solve all sub-goals in a sub-derivation
        def solveSubgoals(s: Subderivation): Option[Statement] = {

          // Optimization: if one of the subgoals failed, to not try the rest!
          // <ugly-imperative-code>
          val results = new ListBuffer[Statement]
          import util.control.Breaks._
          breakable {
            for {subgoal <- s.subgoals} {
              synthesize(subgoal, depth - 1)(stats, nextRules(subgoal, depth - 1))(ind + 1) match {
                case Some(s) => results.append(s)
                case _ => break
              }
            }
          }
          // </ugly-imperative-code>

          val resultStmts = for (r <- results) yield r
          if (resultStmts.size < s.subgoals.size)
          // One of the sub-goals failed: this sub-derivation fails
            None
          else
            handleGuard(s, resultStmts.toList)
        }

        // If stmts is a single guarded statement:
        // if possible, propagate guard to the result of the current goal,
        // otherwise, try to synthesize the else branch and fail if that fails
        def handleGuard(s: Subderivation, stmts: List[Statement]): Option[Statement] =
          stmts match {
            case Guarded(cond, thn) :: Nil =>
              s.kont(stmts) match {
                case g@Guarded(_, _) if depth < config.startingDepth => // Can propagate to upper-level goal
                  Some(g)
                case _ => // Cannot propagate: try to synthesize else branch
                  val goal = s.subgoals.head
                  val newPre = goal.pre.copy(phi = goal.pre.phi && cond.not)
                  // Set starting depth to current depth: new subgoal will start at its own starting depth
                  // to disallow producing guarded statements
                  val newConfig = goal.env.config.copy(startingDepth = depth)
                  val newG = goal.copy(newPre, env = goal.env.copy(config = newConfig))
                  synthesize(newG, depth)(stats, nextRules(newG, depth - 1))(ind) match {
                    case Some(els) => Some(s.kont(List(If(cond, thn, els)))) // successfully synthesized else
                    case _ => None // failed to synthesize else
                  }
              }
            case _ => Some(s.kont(stmts))
          }


        // Invoke the rule
        val allSubderivations = r(goal)
        val goalStr = s"$r: "

        // Filter out subderivations that violate rule ordering
        def goalInOrder(g: Goal): Boolean = {
          g.deriv.outOfOrder(allRules(goal)) match {
            case None => true
            case Some(app) =>
              //              printLog(List((g.deriv.preIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
              //              printLog(List((g.deriv.postIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
              printLog(List((s"$goalStr${RED}Alternative ${g.deriv.applications.head.pp} commutes with earlier ${app.pp}", BLACK)))
              false
          }
        }

        val subderivations = if (config.commute)
          allSubderivations.filter(sub => sub.subgoals.forall(goalInOrder))
        else
          allSubderivations

        if (subderivations.isEmpty) {
          // Rule not applicable: try the rest
          printLog(List((s"$goalStr${RED}FAIL", BLACK)), isFail = true)
          tryRules(rs)
        } else {
          // Rule applicable: try all possible sub-derivations
          val subSizes = subderivations.map(s => s"${s.subgoals.size} sub-goal(s)").mkString(", ")
          val succ = s"SUCCESS at depth $ind, ${subderivations.size} alternative(s) [$subSizes]"
          printLog(List((s"$goalStr$GREEN$succ", BLACK)))
          stats.bumpUpSuccessfulRuleApp()
          if (subderivations.size > 1) {
            printLog(List((s"Trying alternative sub-derivation 1:", CYAN)))
          }
          tryAlternatives(subderivations, 0)
        }
    }

    tryRules(rules)
  }

  private def getIndent(implicit i: Int): String = if (i <= 0) "" else "|  " * i

  private def printLog(sc: List[(String, String)], isFail: Boolean = false)
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