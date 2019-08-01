package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.LanguageUtils.generateFreshVar
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{Statements, _}
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.unification.{SpatialUnification, UnificationGoal}
import org.tygus.suslik.synthesis._

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
  object GuidedWrite extends SynthesisRule  with InvertibleRule {

    override def toString: Ident = "[SE: write]"

    def apply(goal: Goal): Seq[Subderivation] = goal.sketch.uncons match {
      case (cmd@Store(to, offset, new_val), rest) => { // the sketch is a store: apply the rule
        val pre = goal.pre
        val post = goal.post

        val vars_in_new_val: Set[Var] = new_val.collect({
          case Var(_) => true
          case _ => false
        })
        // check that expression is defined during the execution
        for (v <- vars_in_new_val) {
          symExecAssert(goal.isProgramVar(v), s"value `${v.pp}` is read before defined.")
        }

        def matchingHeaplet(h: Heaplet) = h match {
          case PointsTo(h_from, h_offset, _) =>
            SMTSolving.valid(goal.pre.phi ==> ((h_from |+| IntConst(h_offset)) |=| (to |+| IntConst(offset))))
          case _ => false
        }

        findHeaplet(matchingHeaplet, pre.sigma) match {
          case None => throw SynthesisException(cmd.pp + "  Memory is not yet allocated in this address")
          case Some(h: PointsTo) =>
            val newPre = Assertion(pre.phi, (pre.sigma - h) ** PointsTo(to, offset, new_val))
            val subGoal = goal.copy(newPre, sketch = rest)
            val kont: StmtProducer = prependFromSketch(cmd, toString)
            List(Subderivation(List(subGoal), kont))
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

    override def toString: Ident = "[SE: read]"

    /* let to = *(from + offset)
       Check that `from + offset -> e` is in the spatial pre
       and update the pure pre with `to = e`
    */
    def apply(goal:Goal): Seq[Subderivation] = goal.sketch.uncons match {
      case (cmd@Load(to, _, from, offset), rest) => {
        val pre = goal.pre
        val post = goal.post

        symExecAssert(!goal.vars.contains(to), cmd.pp + s"name ${
          to.name
        } is already used.")

        def isMatchingHeaplet: Heaplet => Boolean = {
          case PointsTo(heaplet_from, h_offset, _) =>
            SMTSolving.valid(goal.pre.phi ==> ((heaplet_from |+| IntConst(h_offset)) |=| (from |+| IntConst(offset))))
          case _ => false
        }

        findHeaplet(isMatchingHeaplet, goal.pre.sigma) match {
          case None => {
            throw SymbolicExecutionError("Invalid read: no matching heaplet: " + cmd.pp)
          }
          case Some(PointsTo(_, _, a)) =>
            val tpy = a.getType(goal.gamma).get // the precondition knows better than the statement
            val subGoal = goal.copy(
              pre = pre.copy(phi = pre.phi && (to |=| a)),
              post = post.copy(phi = post.phi && (to |=| a)),
              sketch = rest).addProgramVar(to, tpy)
            val kont: StmtProducer = prependFromSketch(cmd, toString)
            List(Subderivation(List(subGoal), kont))
          case Some(h) =>
            throw SynthesisException(cmd.pp + s" Read rule matched unexpected heaplet ${
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

    override def toString: Ident = "[SE: alloc]"

    def apply(goal: Goal): Seq[Subderivation] = goal.sketch.uncons match {
      case (cmd@Malloc(y, tpy, sz), rest) => {
        val pre = goal.pre
        symExecAssert(!goal.vars.contains(y), cmd.pp + s"name ${
          y.name
        } is already used.")

        val freshChunks = for {
          off <- 0 until sz
          z = generateFreshVar(goal, s"$$ tmp_$off")
        } // yield PointsTo(y, off, z)
          yield PointsTo(y, off, IntConst(MallocInitVal)) // because tons of variables slow down synthesis.
        val freshBlock = Block(y, sz)
        val newPre = Assertion(pre.phi, SFormula(pre.sigma.chunks ++ freshChunks ++ List(freshBlock)))
        val subGoal = goal.copy(newPre, sketch = rest).addProgramVar(y, tpy)
        val kont: StmtProducer = prependFromSketch(cmd, toString)
        List(Subderivation(List(subGoal), kont))
      }
      case _ => Nil
    }
  }

  /*
  When the first statement in the sketch is a free,
  modify the goal's precondition to account for the de-allocation
  */
  object GuidedFree extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "[SE: free]"

    def findNamedHeaplets(goal: Goal, name:Var): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))
      def noGhostsAndIsBlock(h: Heaplet): Boolean = h match {
        case b@Block(loc, sz) => noGhosts(b) && SMTSolving.valid(goal.pre.phi ==> (loc |=| name))
        case _ => false
      }

      findBlockAndChunks(noGhostsAndIsBlock, _ => true, goal.pre.sigma)
    }

    def apply(goal: Goal): Seq[Subderivation] = goal.sketch.uncons match {
      case (cmd@Free(x), rest) => {
        val pre = goal.pre
        symExecAssert(goal.programVars.contains(x), cmd.pp + s"value `${x.name}` is not defined.")
        // todo: make findNamedHeaplets find parts with different name but equal values wrt pure part
        findNamedHeaplets(goal, x) match {
          case None => throw SymbolicExecutionError("command " + cmd.pp + " is invalid")
          case Some((h@Block(_, _), pts)) =>
            val newPre = Assertion(pre.phi, pre.sigma - h - pts)
            val subGoal = goal.copy(newPre, sketch = rest)
            val kont: StmtProducer = prependFromSketch(cmd, toString)
            List(Subderivation(List(subGoal), kont))
          case Some(what) => throw SynthesisException("Unexpected heaplet " + what + " found while executing " + cmd.pp)
        }
      }
      case _ => Nil
    }
  }

  object GuidedCall extends SynthesisRule with UnfoldingPhase {

    override def toString: Ident = "[SE: call]"

    def apply(goal:Goal): Seq[Subderivation] = goal.sketch.uncons match {
      case (cmd@Call(to, fun, actuals), rest) => {
        symExecAssert(goal.env.functions.contains(fun.name), s"Undefined function in function call: ${cmd.pp}")
        val actualVars = actuals.flatMap(_.vars).toSet
        symExecAssert(actualVars.forall(x => goal.isProgramVar(x)), s"Undefined or ghost variables in function call arguments: ${cmd.pp}")
        val _f = goal.env.functions(fun.name)
        symExecAssert(_f.params.size == actuals.size, s" Function ${_f.name} takes ${_f.params.size} arguments, but ${actuals.size} given: ${cmd.pp}")
        val f = _f.refreshExistentials(goal.vars)

        val lilHeap = f.pre.sigma
        val largHeap = goal.pre.sigma

        val subgoals = for {
          // Find all subsets of the goal's pre that might be unified
          largSubHeap <- findLargestMatchingHeap(lilHeap, largHeap)
          callSubPre = goal.pre.copy(sigma = largSubHeap)

          // Try to unify f's precondition and found goal pre's subheaps
          // We don't care if f's params are replaced with ghosts, we already checked earlier that actuals are not ghost
          source = UnificationGoal(f.pre, Set.empty)
          target = UnificationGoal(callSubPre, Set.empty)
          sub <- {
            SpatialUnification.unify(target, source).toList
          }

          // Check that actuals supplied in the code are equal to those implied by the substitution
          argsValid = mkConjunction(actuals.zip(f.params.map(_._2.subst(sub))).map { case (x, y) => x |=| y}.toList)
          if SMTSolving.valid(goal.pre.phi ==> (argsValid && f.pre.phi.subst(sub)))
          callGoal <- UnfoldingRules.CallRule.mkCallGoal(f, sub, callSubPre, goal, also_gen_locked = false)
        } yield {
          callGoal.copy(sketch = rest)
        }
        symExecAssert(subgoals.nonEmpty, cmd.pp + " function can't be called.")
        assert(subgoals.size == 1, "Unexpected: function call produced multiple subgoals: " + cmd.pp)
        List(Subderivation(subgoals, prepend(cmd, toString)))
      }
      case _ => Nil
    }

  }

  object Conditional extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "[SE: cond]"

    private def kont(cond: Expr): StmtProducer = stmts => {
      ruleAssert(stmts.length == 2, s"Conditional rule expected two subgoals got ${stmts.length}")
      If(cond, stmts.head, stmts.last)
    }


    def apply(goal: Goal): Seq[Subderivation] = goal.sketch.uncons match {
      case (cmd@If(cond, tb, eb), Skip) => {
        val pre = goal.pre
        val thenGoal = goal.copy(Assertion(pre.phi && cond, pre.sigma), sketch = tb)
        val elseGoal = goal.copy(Assertion(pre.phi && cond.not, pre.sigma), sketch = eb)
        List(Subderivation(List(thenGoal, elseGoal), kont(cond)))
      }
      case (cmd@If(cond, tb, eb), _) => {
        throw SynthesisException("Found conditional in the middle of the program. Conditionals only allowed at the end.")
      }
      case _ => Nil
    }
  }


  object Open extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "[SE: open]"

    // Like the synthesis version of open,
    // but selects a single case, whose selector is implied by the precondition
    def apply(goal: Goal): Seq[Subderivation] = {
      for {
        h <- goal.pre.sigma.chunks
        (selector, subgoal) <- UnfoldingRules.Open.mkInductiveSubGoals(goal, h).getOrElse(Nil)
        if SMTSolving.valid(goal.pre.phi ==> selector)
      } yield Subderivation(List(subgoal), pureKont(toString))
    }
  }
}