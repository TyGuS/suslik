package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.LanguageUtils
import org.tygus.suslik.LanguageUtils.generateFreshVar
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.Load
import org.tygus.suslik.language.{Statements, _}
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis._
import sun.reflect.generics.reflectiveObjects.NotImplementedException

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

    /* let to = *(from + offset) */
    /* if *(from + offset) is var, then substitute and update pure part,
       else only update pure part.
       No problems found so far
       Doesn't comply with any rules, but works without modifications of synthesis process.
    * */
    def apply(goal:Goal): Seq[Subderivation] = goal.sketch.uncons match {
      case (cmd@Load(to, tpy, from, offset), rest) => {
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
            throw SymbolicExecutionError(cmd.pp + " Invalid command: right part is not defined.")
          }
          case Some(PointsTo(_, _, value@Var(_))) =>
            // substitute, and update pure part
            val subst_pre = pre.subst(value, to)
            val subst_post = post.subst(value, to)
            val new_pre = subst_pre.copy(phi = subst_pre.phi && (to |=| value))
            val new_post = subst_post.copy(phi = subst_post.phi && (to |=| value))
            val subGoal = goal.copy(pre = new_pre, post = new_post, sketch = rest).addProgramVar(to, tpy)
            //          val subGoal = goal.copy(pre.copy(phi = pre.phi && (to |=| a) ), post = post.copy(phi = post.phi && (to |=| a))).addProgramVar(to, tpy)
            val kont: StmtProducer = prependFromSketch(cmd, toString)
            List(Subderivation(List(subGoal), kont))
          case Some(PointsTo(_, _, a)) =>
            // only update pure part
            //          val subGoal = goal.copy(pre.subst(a, to), post = post.subst(a, to)).addProgramVar(to, tpy)
            val subGoal = goal.copy(pre.copy(phi = pre.phi && (to |=| a)), post = post.copy(phi = post.phi && (to |=| a)), sketch = rest).addProgramVar(to, tpy)
            val kont: StmtProducer = prependFromSketch(cmd, toString)
            List(Subderivation(List(subGoal), kont))
          case Some(h) =>
            throw SynthesisException(cmd.pp + s" Read rule matched unexpected heaplet ${
              h.pp
            }")
            Nil
        }
      }
      case _ => Nil
    }

    /* let to = *(from + offset) */
    /* Substitute to by new value
    * Problem: it destroys vars. For example, in program
      len x = *w
      let y = *w
      let z = *x <--- error, because previous line destroyed x
      complies with the modified SSL rule (which is wrong, because ^^^)
    * */
    def symbolicExecution_subst(goal:Goal, cmd:Load):Goal = {
      val pre = goal.pre
      val post = goal.post
      val Load(to, tpy, from, offset) = cmd
      symExecAssert(!goal.vars.contains(to), cmd.pp + s"name ${to.name} is already used.")
      def isMatchingHeaplet: Heaplet => Boolean = {
        case PointsTo(heaplet_from, h_offset, _) =>
          SMTSolving.valid(goal.pre.phi ==> ((heaplet_from |+| IntConst(h_offset)) |=| (from |+| IntConst(offset))))
        case _ => false
      }
      findHeaplet(isMatchingHeaplet, goal.pre.sigma) match {
        case None => throw SymbolicExecutionError(cmd.pp + " Invalid command: right part is not defined.")
        case Some(PointsTo(_, _, a@Var(_))) =>
          val subGoal = goal.copy(pre.subst(a, to), post = post.subst(a, to)).addProgramVar(to, tpy)
          subGoal
        case Some(h) =>
          throw SynthesisException(cmd.pp + s" Read rule matched unexpected heaplet ${h.pp}")
      }
    }

    /* let to = *(from + offset) */
    /* Puts additional clause `to == *(from + offset)` in pure part, adds `to` to program vars
    * problem 1: this new var might be unused during synthesis, and `let to = *(from + offset)` can be synthesized again
    * problem 2: computations take forever ("sorted list: insert an element with holes" takes 631 sec)
    * (Both solved by augmenting synthesis read rule with `&& ! alreadyLoaded(a)`)
    * complies with `Symbolic Execution with Separation Logic` paper
    * http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.64.2006&rep=rep1&type=pdf
    * problem 3: it doesn't transform the heap in the same way as synthesis does ==> can't call functions sometimes.
    * "sorted list: insert an element complete prog" fails
    * (not solved)
    * */
    def symbolicExecution_phi(goal:Goal, cmd:Load):Goal = {
      val pre = goal.pre
      val post = goal.post
      val Load(to, tpy, from, offset) = cmd
      symExecAssert(!goal.vars.contains(to), cmd.pp + s"name ${to.name} is already used.")
      def isMatchingHeaplet: Heaplet => Boolean = {
        case PointsTo(heaplet_from, h_offset, _) =>
          SMTSolving.valid(goal.pre.phi ==> ((heaplet_from |+| IntConst(h_offset)) |=| (from |+| IntConst(offset))))
        case _ => false
      }
      findHeaplet(isMatchingHeaplet, goal.pre.sigma) match {
        case None => throw SymbolicExecutionError(cmd.pp + " Invalid command: right part is not defined.")
        case Some(PointsTo(_, _, a)) =>
          val subGoal = goal.copy(pre.copy(phi=pre.phi && (to |=| a)), post = post.copy(phi=post.phi && (to |=| a))).addProgramVar(to, tpy)
          subGoal
        case Some(h) =>
          throw SynthesisException(cmd.pp + s" Read rule matched unexpected heaplet ${h.pp}")
      }
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
        val deriv = goal.deriv
        val Free(x) = cmd
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

}