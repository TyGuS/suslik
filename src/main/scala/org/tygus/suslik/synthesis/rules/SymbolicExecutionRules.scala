package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{Statements, _}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.unification.SpatialUnification
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Symbolic execution rules are guided by the sketch.
  * @author Nadia Polikarpova, Roman Shchedrin
  */

object SymbolicExecutionRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-symex"

  import Statements._

  /*
  When the first statement in the sketch is a store *(to + offset) = e,
  modify the goal's precondition to account for the store if possible
  */
  object GuidedWrite extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "SE-Write"

    def apply(goal: Goal): Seq[RuleResult] = goal.sketch.uncons match {
      case (cmd@Store(to, offset, new_val), rest) => { // the sketch is a store: apply the rule
        val pre = goal.pre
        val post = goal.post

        val vars_in_new_val: Set[Var] = new_val.collect({
          case Var(_) => true
          case _ => false
        })
        // check that expression is defined during the execution
        for (v <- vars_in_new_val) {
          synAssert(goal.isProgramVar(v), s"value `${v.pp}` is read before defined.")
        }

        def matchingHeaplet(h: Heaplet) = h match {
          case PointsTo(h_from, h_offset, _) =>
            SMTSolving.valid(goal.pre.phi ==> ((h_from |+| IntConst(h_offset)) |=| (to |+| IntConst(offset))))
          case _ => false
        }

        findHeaplet(matchingHeaplet, pre.sigma) match {
          case None => throw SynthesisException("Write into unknown location: " + cmd.pp)
          case Some(h: PointsTo) =>
            val newPre = Assertion(pre.phi, (pre.sigma - h) ** PointsTo(to, offset, new_val))
            val subGoal = goal.spawnChild(newPre, sketch = rest)
            val kont: StmtProducer = PrependFromSketchProducer(cmd)
            List(RuleResult(List(subGoal), kont, Footprint(singletonHeap(h), emp), this))
          case Some(h) =>
            ruleAssert(false, s"Write rule matched unexpected heaplet ${h.pp}")
            Nil
        }
      }
      case _ => Nil // otherwise, this rule is not applicable
    }
  }


  /*
  When the first statement in the sketch is a load let to = *(from + offset),
  modify the goal's precondition to account for the load if possible
  */
  object GuidedRead extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "SE-Read"

    /* let to = *(from + offset)
       Check that `from + offset -> e` is in the spatial pre
       and update the pure pre with `to = e`
    */
    def apply(goal:Goal): Seq[RuleResult] = goal.sketch.uncons match {
      case (cmd@Load(to, _, from, offset), rest) => {
        val pre = goal.pre
        val post = goal.post

        synAssert(!goal.vars.contains(to), cmd.pp + s"name ${
          to.name
        } is already used.")

        def isMatchingHeaplet: Heaplet => Boolean = {
          case PointsTo(heaplet_from, h_offset, _) =>
            SMTSolving.valid(goal.pre.phi ==> ((heaplet_from |+| IntConst(h_offset)) |=| (from |+| IntConst(offset))))
          case _ => false
        }

        findHeaplet(isMatchingHeaplet, goal.pre.sigma) match {
          case None => {
            throw SynthesisException("Read from unknown location: " + cmd.pp)
          }
          case Some(h@PointsTo(_, _, a)) =>
            val tpy = a.getType(goal.gamma).get // the precondition knows better than the statement
            val subGoal = goal.spawnChild(
              pre = pre.copy(phi = pre.phi && (to |=| a)),
              post = post.copy(phi = post.phi && (to |=| a)),
              gamma = goal.gamma + (to -> tpy),
              programVars = to :: goal.programVars,
              sketch = rest)
            val kont: StmtProducer = PrependFromSketchProducer(cmd)
            List(RuleResult(List(subGoal), kont, Footprint(singletonHeap(h), emp), this))
          case Some(h) =>
            throw SymbolicExecutionError(cmd.pp + s" Read rule matched unexpected heaplet ${
              h.pp
            }")
        }
      }
      case _ => Nil
    }
  }

  /*
  When the first statement in the sketch is a malloc,
  modify the goal's precondition to account for the allocation
  */
  object GuidedAlloc extends SynthesisRule with InvertibleRule {
    val MallocInitVal = 666

    override def toString: Ident = "SE-Alloc"

    def apply(goal: Goal): Seq[RuleResult] = goal.sketch.uncons match {
      case (cmd@Malloc(y, tpy, sz), rest) => {
        val pre = goal.pre
        synAssert(!goal.vars.contains(y), cmd.pp + s"name ${
          y.name
        } is already used.")

        val freshChunks = for {
          off <- 0 until sz
        } yield PointsTo(y, off, IntConst(MallocInitVal)) // because tons of variables slow down synthesis.
        val freshBlock = Block(y, sz)
        val newPre = Assertion(pre.phi, mkSFormula(pre.sigma.chunks ++ freshChunks ++ List(freshBlock)))
        val subGoal = goal.spawnChild(newPre,
          gamma = goal.gamma + (y -> tpy),
          programVars = y :: goal.programVars,
          sketch = rest)
        val kont: StmtProducer = PrependFromSketchProducer(cmd)
        List(RuleResult(List(subGoal), kont, goal.allHeaplets, this))
      }
      case _ => Nil
    }
  }

  /*
  When the first statement in the sketch is a free,
  modify the goal's precondition to account for the de-allocation
  */
  object GuidedFree extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "SE-Free"

    def findNamedHeaplets(goal: Goal, name:Var): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))
      def noGhostsAndIsBlock(h: Heaplet): Boolean = h match {
        case b@Block(loc, sz) => noGhosts(b) && SMTSolving.valid(goal.pre.phi ==> (loc |=| name))
        case _ => false
      }

      findBlockAndChunks(noGhostsAndIsBlock, _ => true, goal.pre.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = goal.sketch.uncons match {
      case (cmd@Free(x), rest) => {
        val pre = goal.pre
//        symExecAssert(goal.programVars.contains(x), cmd.pp + s"value `${x.name}` is not defined.")
        // todo: make findNamedHeaplets find parts with different name but equal values wrt pure part
        findNamedHeaplets(goal, x) match {
          case None => throw SynthesisException("No block at this location or some record fields are unknown: " + cmd.pp)
          case Some((h@Block(_, _), pts)) =>
            val newPre = Assertion(pre.phi, pre.sigma - h - mkSFormula(pts.toList))
            val subGoal = goal.spawnChild(newPre, sketch = rest)
            val kont: StmtProducer = PrependFromSketchProducer(cmd)
            List(RuleResult(List(subGoal), kont, goal.allHeaplets, this))
          case Some(what) => throw SymbolicExecutionError("Unexpected heaplet " + what + " found while executing " + cmd.pp)
        }
      }
      case _ => Nil
    }
  }

  object GuidedCall extends SynthesisRule with UnfoldingPhase with InvertibleRule {

    override def toString: Ident = "SE-Call"

    def apply(goal:Goal): Seq[RuleResult] = goal.sketch.uncons match {
      case (cmd@Call(fun, actuals, _), rest) => {
        val topLevelGoal = goal.companionCandidates.last
        val funEnv = goal.env.functions + (goal.fname -> topLevelGoal.toFunSpec)

        synAssert(funEnv.contains(fun.name), s"Undefined function in function call: ${cmd.pp}")
        val actualVars = actuals.flatMap(_.vars).toSet
        synAssert(actualVars.forall(x => goal.isProgramVar(x)), s"Undefined or ghost variables in function call arguments: ${cmd.pp}")
        val _f = funEnv(fun.name)
        synAssert(_f.params.size == actuals.size, s" Function ${_f.name} takes ${_f.params.size} arguments, but ${actuals.size} given: ${cmd.pp}")
        val f = _f.refreshExistentials(goal.vars)

        val lilHeap = f.pre.sigma
        val largHeap = goal.pre.sigma

        val subgoals = for {
          // Find all subsets of the goal's pre that might be unified
          largSubHeap <- findLargestMatchingHeap(lilHeap, largHeap)
          callSubPre = goal.pre.copy(sigma = largSubHeap)

          sourceAsn = f.pre
          targetAsn = callSubPre

          // Try to unify f's precondition and found goal pre's subheaps
          // We don't care if f's params are replaced with ghosts, we already checked earlier that actuals are not ghost
          sub <- SpatialUnification.unify(targetAsn, sourceAsn).toList

          // Checking ghost flow for a given substitution
          sourceParams = f.params.map(_._2).toSet
          targetParams = goal.programVars.toSet
          if SpatialUnification.checkGhostFlow(sub, targetAsn, targetParams, sourceAsn, sourceParams)

          // Check that actuals supplied in the code are equal to those implied by the substitution
          argsValid = PFormula(actuals.zip(f.params.map(_._2.subst(sub))).map { case (x, y) => x |=| y}.toSet)
          if SMTSolving.valid(goal.pre.phi ==> (argsValid && f.pre.phi.subst(sub)))
          callGoal <- UnfoldingRules.CallRule.mkCallGoal(f, sub, callSubPre, goal)
        } yield {
          callGoal.copy(sketch = rest)
        }
        symExecAssert(subgoals.nonEmpty, cmd.pp + " function can't be called.")
        assert(subgoals.size == 1, "Unexpected: function call produced multiple subgoals: " + cmd.pp)
        List(RuleResult(subgoals, PrependProducer(cmd), goal.allHeaplets, this))
      }
      case _ => Nil
    }

  }

  object Conditional extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "SE-Cond"


    def apply(goal: Goal): Seq[RuleResult] = goal.sketch.uncons match {
      case (If(cond, tb, eb), Skip) => {
        val unknown = cond.vars.filterNot(goal.isProgramVar)
        symExecAssert(unknown.isEmpty, s"Unknown variables in condition: ${unknown.map(_.pp).mkString(",")}")
        val pre = goal.pre
        val thenGoal = goal.spawnChild(Assertion(pre.phi && cond, pre.sigma), sketch = tb)
        val elseGoal = goal.spawnChild(Assertion(pre.phi && cond.not, pre.sigma), sketch = eb)
        List(RuleResult(List(thenGoal, elseGoal), BranchProducer(List(cond, cond.not)), goal.allHeaplets, this))
      }
      case (If(_, _, _), _) => {
        throw SynthesisException("Found conditional in the middle of the program. Conditionals only allowed at the end.")
      }
      case _ => Nil
    }
  }


  object Open extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "SE-Open"

    // Like the synthesis version of open,
    // but selects a single case, whose selector is implied by the precondition
    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        h <- goal.pre.sigma.chunks
        (selGoals, _) <- UnfoldingRules.Open.mkInductiveSubGoals(goal, h).toList
        (selector, subGoal) <- selGoals
        if SMTSolving.valid(goal.pre.phi ==> selector)
      } yield RuleResult(List(subGoal), IdProducer, goal.allHeaplets, this)
    }
  }
}