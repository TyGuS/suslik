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
  * Operational rules emit statement that operate of flat parts of the heap.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object OperationalRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-operational"

  import Statements._

  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; x.f -> l' * P} ; {ψ ; x.f -> l' * Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l' * Q} ---> *x.f := l' ; S

  */
  object WriteRuleOld extends SynthesisRule with FlatPhase {

    override def toString: Ident = "[Op: write-old]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@(Var(_)), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && noGhosts(hr)

      findMatchingHeaplets(noGhosts, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@(PointsTo(x@Var(_), offset, e1)), hr@(PointsTo(_, _, e2)))) =>
          if (e1 == e2) {
            return Nil
          } // Do not write if RHSs are the same

          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi, goal.post.sigma - hr)
          val subGoal = goal.copy(newPre, newPost)
          val kont: StmtProducer = prepend(Store(x, offset, e2), toString)

          List(Subderivation(List(subGoal), kont))
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }
  }


  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; P} ; {ψ ; x.f -> Y * Q} ---> S   GV(l) = Ø  Y is fresh
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; P} ; {ψ ; x.f -> l * Q} ---> S; *x.f := l

  */
  object WriteRule extends SynthesisRule with FlatPhase with InvertibleRule {

    override def toString: Ident = "[Op: write]"

    // *(to + offset) = e
    def symbolicExecution(goal: Goal, cmd:Store): Goal = {
      val pre = goal.pre
      val post = goal.post
      val Store(to, offset, new_val) = cmd

      val vars_in_new_val:Set[Var] = new_val.collect({
        case Var(_) => true
        case _ => false
      })
      // check that expression is defined during the execution
      for(v<-vars_in_new_val){
        symExecAssert(goal.isProgramVar(v), s"value `${v.pp}` is read before defined.")
      }

      def matchingHeaplet(h:Heaplet) = h match{
        case PointsTo(h_from, h_offset, _) =>
          SMTSolving.valid(goal.pre.phi ==> ((h_from |+| IntConst(h_offset)) |=| (to |+| IntConst(offset))))
        case _ => false
      }

      findHeaplet(matchingHeaplet, pre.sigma) match {
        case None => throw SynthesisException(cmd.pp + "  Memory is not yet allocated in this address")
        case Some(h:PointsTo) =>
          val newPre = Assertion(pre.phi, (pre.sigma - h) ** PointsTo(to, offset, new_val))
          val subGoal = goal.copy(pre = newPre)
          subGoal
        case Some(h) =>
          ruleAssert(false, s"Write rule matched unexpected heaplet ${h.pp}")
          goal
      }
    }

    def apply(goal: Goal): Seq[Subderivation] = {

      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      findHeaplet(noGhosts, post.sigma) match {
        case None => Nil
        case Some(h@PointsTo(x@Var(_), offset, l)) =>

          // Same heaplet in pre: no point in writing
          if (pre.sigma.chunks.contains(h)) return Nil

          val y = generateFreshVar(goal)

          val newPost = Assertion(post.phi, (post.sigma - h) ** PointsTo(x, offset, y))
          val subGoal = goal.copy(post = newPost)
          val kont: StmtProducer = append(Store(x, offset, l), toString)
          List(Subderivation(List(subGoal), kont))
        case Some(h) =>
          ruleAssert(false, s"Write rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }
  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{φ ; x -> A * P} ; [y/A]{ψ ; Q} ---> S
      ---------------------------------------------------------------- [read]
             Γ ; {φ ; x.f -> A * P} ; {ψ ; Q} ---> let y := *x.f ; S
  */
  object ReadRule extends SynthesisRule with AnyPhase with InvertibleRule {

    override def toString: Ident = "[Op: read]"

    /* let to = *(from + offset) */
    /* if *(from + offset) is var, then substitute and update pure part,
       else only update pure part.
       No problems found so far
       Doesn't comply with any rules, but works without modifications of synthesis process.
    * */
    def symbolicExecution_phi_and_subst_if_can(goal:Goal, cmd:Load):Goal = {
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
        case None => {
          throw SymbolicExecutionError(cmd.pp + " Invalid command: right part is not defined.")
        }
        case Some(PointsTo(_, _, value@Var(_))) =>
          // substitute, and update pure part
          val subst_pre = pre.subst(value, to)
          val subst_post = post.subst(value, to)
          val new_pre = subst_pre.copy(phi = subst_pre.phi &&  (to |=| value))
          val new_post= subst_post.copy(phi = subst_post.phi &&  (to |=| value))
          val subGoal = goal.copy(pre = new_pre, post = new_post).addProgramVar(to, tpy)
//          val subGoal = goal.copy(pre.copy(phi = pre.phi && (to |=| a) ), post = post.copy(phi = post.phi && (to |=| a))).addProgramVar(to, tpy)
          subGoal
        case Some(PointsTo(_, _, a)) =>
          // only update pure part
          //          val subGoal = goal.copy(pre.subst(a, to), post = post.subst(a, to)).addProgramVar(to, tpy)
          val subGoal = goal.copy(pre.copy(phi = pre.phi && (to |=| a) ), post = post.copy(phi = post.phi && (to |=| a))).addProgramVar(to, tpy)
          subGoal
        case Some(h) =>
          throw SynthesisException(cmd.pp + s" Read rule matched unexpected heaplet ${h.pp}")
      }
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

//    def symbolicExecution: (Goal, Load) => Goal = symbolicExecution_trying_to_be_smart
//    def symbolicExecution: (Goal, Load) => Goal = symbolicExecution_subst
    def symbolicExecution: (Goal, Load) => Goal = symbolicExecution_phi

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post
      val gamma = goal.gamma

      def alreadyLoaded(a:Var): Boolean = {
        goal.programVars.exists(b => SMTSolving.valid(goal.pre.phi ==> (a |=| b)))
      }

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, a@Var(_)) =>
           !goal.isGhost(x) && goal.isGhost(a) && ! alreadyLoaded(a)
        case _ => false
      }

      findHeaplet(isGhostPoints, goal.pre.sigma) match {
        case None => Nil
        case Some(PointsTo(x@Var(_), offset, a@Var(_))) =>
          val y = generateFreshVar(goal, a.name)
          val tpy = goal.getType(a)

          val subGoal = goal.copy(pre.subst(a, y), post = post.subst(a, y)).addProgramVar(y,tpy)
          val kont: StmtProducer = prepend(Load(y, tpy, x, offset), toString)
          List(Subderivation(List(subGoal), kont))
        case Some(h) =>
          ruleAssert(false, s"Read rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }

  /*
  Alloc rule: allocate memory for an existential block

           X ∈ GV(post) / GV (pre)        y, Ai fresh
         Γ ; {φ ; y -> (A0 .. An) * P} ; {ψ ; [y/X]Q} ---> S
     -------------------------------------------------------------- [alloc]
     Γ ; {φ ; P} ; {ψ ; block(X, n) * Q} ---> let y = malloc(n); S
  */
  object AllocRule extends SynthesisRule with FlatPhase {
    val MallocInitVal = 666

    override def toString: Ident = "[Op: alloc]"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      def isExistBlock: Heaplet => Boolean = {
        case Block(x@Var(_), _) => goal.isExistential(x)
        case _ => false
      }

      findBlockAndChunks(isExistBlock, _ => true, goal.post.sigma)
    }

    def symbolicExecution(goal: Goal, cmd:Malloc): Goal = {
      val Malloc(y, tpy, sz) = cmd
      val pre = goal.pre
      val post = goal.post
      symExecAssert(!goal.vars.contains(y), cmd.pp + s"name ${y.name} is already used.")

      val freshChunks = for {
        off <- 0 until sz
        z = generateFreshVar(goal, s"$$tmp_$off")
      }// yield PointsTo(y, off, z)
       yield PointsTo(y, off, IntConst(MallocInitVal)) // because tons of variables slow down synthesis.
      val freshBlock = Block(y, sz)
      val newPre = Assertion(pre.phi, SFormula(pre.sigma.chunks ++ freshChunks ++ List(freshBlock)))
      val subGoal = goal.copy(newPre, post).addProgramVar(y, tpy)
      subGoal
    }

    def apply(goal: Goal): Seq[Subderivation] = {

      val pre = goal.pre
      val post = goal.post
      val gamma = goal.gamma
      val deriv = goal.deriv

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), sz), pts)) =>
          val y = generateFreshVar(goal, x.name)
          val tpy = LocType

          val freshChunks = for {
            off <- 0 until sz
            z = generateFreshVar(goal, s"$$tmp_$off") // without s"$$tmp_$off" all names will be same
          } // yield PointsTo(y, off, z)
            yield PointsTo(y, off, IntConst(MallocInitVal))
          val freshBlock = Block(x, sz).subst(x, y)
          val newPre = Assertion(pre.phi, SFormula(pre.sigma.chunks ++ freshChunks ++ List(freshBlock)))

          val postFootprint = pts.map(p => deriv.postIndex.lastIndexOf(p)).toSet + deriv.postIndex.lastIndexOf(h)
          val ruleApp = saveApplication((Set.empty, postFootprint), deriv)

          val subGoal = goal.copy(newPre, post.subst(x, y), newRuleApp = Some(ruleApp)).addProgramVar(y, tpy)
          val kont: StmtProducer = prepend(Malloc(y, tpy, sz), toString)
          List(Subderivation(List(subGoal), kont))
        case _ => Nil
      }
    }

  }

  /*
  Free rule: free a non-ghost block from the pre-state

                     Γ ; {φ ; P} ; {ψ ; Q} ---> S     GV(li) = Ø
   ------------------------------------------------------------------------ [free]
   Γ ; {φ ; block(x, n) * x -> (l1 .. ln) * P} ; { ψ ; Q } ---> free(x); S
*/
  object FreeRule extends SynthesisRule with FlatPhase {

    override def toString: Ident = "[Op: free]"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))
      def noGhostsAndIsBlock(h: Heaplet): Boolean = h match {
        case b:Block => noGhosts(b)
        case _ => false
      }

      findBlockAndChunks(noGhostsAndIsBlock, noGhosts, goal.pre.sigma)
    }

    def findNamedHeaplets(goal: Goal, name:Var): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))
      def noGhostsAndIsBlock(h: Heaplet): Boolean = h match {
        case b@Block(loc, sz) => noGhosts(b) && SMTSolving.valid(goal.pre.phi ==> (loc |=| name))
        case _ => false
      }

      findBlockAndChunks(noGhostsAndIsBlock, _ => true, goal.pre.sigma)
    }

    def symbolicExecution(goal:Goal, cmd:Free): Goal ={
      val pre = goal.pre
      val deriv = goal.deriv
      val Free(x) = cmd
      symExecAssert(goal.programVars.contains(x), cmd.pp + s"value `${x.name}` is not defined.")
      // todo: make findNamedHeaplets find parts with different name but equal values wrt pure part
      findNamedHeaplets(goal, x) match {
        case None => throw SymbolicExecutionError("command " + cmd.pp + " is invalid")
        case Some((h@Block(_, _), pts)) =>
          val newPre = Assertion(pre.phi, pre.sigma - h - pts)
          val subGoal = goal.copy(newPre)
          subGoal
        case Some(what) => throw SynthesisException("Unexpected heaplet " + what + " found while executing " + cmd.pp)
      }
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val deriv = goal.deriv

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), _), pts)) =>
          val newPre = Assertion(pre.phi, pre.sigma - h - pts)

          // Collecting the footprint
          val preFootprint = pts.map(p => deriv.preIndex.lastIndexOf(p)).toSet + deriv.preIndex.lastIndexOf(h)
          val ruleApp = saveApplication((preFootprint, Set.empty), deriv)

          val subGoal = goal.copy(newPre, newRuleApp = Some(ruleApp))
          val kont: StmtProducer = prepend(Free(x), toString)

          List(Subderivation(List(subGoal), kont))
        case Some(_) => Nil
      }
    }

  }

}