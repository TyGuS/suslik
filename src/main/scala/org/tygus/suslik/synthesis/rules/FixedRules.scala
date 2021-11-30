package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions
import org.tygus.suslik.language.Expressions.{BinaryExpr, Expr, NilPtr, OpBoolEq, OpEq, OpIntervalEq, OpSetEq, Var}
import org.tygus.suslik.language.Statements.{Load, Skip, Store}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.{Heaplet, PFormula, PointsTo, SFormula, SepLogicUtils, Specifications}
import org.tygus.suslik.synthesis.{ConstProducer, ExtractHelper, IdProducer, PrependProducer, PureEntailmentProducer, StmtProducer, SubstProducer, SubstVarProducer, SynthesisException}
import org.tygus.suslik.synthesis.rules.LogicalRules.EmpRule
import org.tygus.suslik.synthesis.rules.LogicalRules.SubstLeft.findConjunctAndRest
import org.tygus.suslik.synthesis.rules.OperationalRules.ReadRule.freshVar
import org.tygus.suslik.synthesis.rules.OperationalRules.{findHeaplet, ruleAssert, sameLhs, sameRhs}
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, SynthesisRule}
import org.tygus.suslik.synthesis.rules.UnificationRules.SubstRight.findConjunctAndRest

import scala.collection.generic.CanBuildFrom
import scala.collection.immutable
import scala.collection.immutable.SortedSet


sealed trait FixedRules extends SynthesisRule {
  def nextRule: List[FixedRules]
}

object FixedRules {

  def to_iterator (rules: List[FixedRules]) : Iterator[FixedRules] =
    rules.flatMap(rule => rule :: rule.nextRule).toIterator

  case object Emp extends SynthesisRule with FixedRules {

    override def nextRule: List[FixedRules] = List()

    override def apply(goal: Specifications.Goal): Seq[Rules.RuleResult] =
      EmpRule.apply(goal)
  }

  case class StarPartial(vars: List[(String,String)]) extends SynthesisRule with FixedRules {
    val conjuncts : SortedSet[Expressions.Expr] = vars.map({case (x,y) => (Var(x) |/=| Var(y))}).to[SortedSet]

    override def nextRule: List[FixedRules] = List()

    def extendPure(p: PFormula, s: SFormula): PFormula = {
      val ptrs = (for (PointsTo(x, o, _) <- s.chunks) yield (o, x)).groupBy(_._1).mapValues(_.map(_._2))
      // All pairs of pointers
      val pairs = for (o <- ptrs.keySet; x <- ptrs(o); y <- ptrs(o) if x != y) yield (x, y)
      val newPairs = pairs.filter {
        case (x, y) => !p.conjuncts.contains(x |/=| y) && !p.conjuncts.contains(y |/=| x) && conjuncts.contains(x |/=| y)
      }
      PFormula(newPairs.map { case (x, y) => x |/=| y })
    }

    override def apply(goal: Specifications.Goal): Seq[Rules.RuleResult] = {
      if (goal.pre.phi == pFalse) return Nil
      val kont = IdProducer >> ExtractHelper(goal)

      val newPrePhi = extendPure(goal.pre.phi, goal.pre.sigma)
      val newPostPhi = extendPure(goal.pre.phi && goal.post.phi, goal.post.sigma)

      if (newPrePhi.conjuncts.isEmpty && newPostPhi.conjuncts.isEmpty) return Nil
      val newPre = goal.pre.copy(phi = goal.pre.phi && newPrePhi)
      val newPost = goal.post.copy(phi = goal.post.phi && newPostPhi)
      val newGoal = goal.spawnChild(newPre, newPost)
      List(RuleResult(List(newGoal), kont, org.tygus.suslik.synthesis.rules.LogicalRules.StarPartial, goal))
    }
  }

  case class NilNotLval(vars: List[String]) extends SynthesisRule with FixedRules {
    val notLvalVars = vars.to[SortedSet]

    override def nextRule: List[FixedRules] = List()


    def apply(goal: Goal): Seq[RuleResult] = {
      if (goal.pre.phi == pFalse) return Nil

      // Find pointers in `a` that are not yet known to be non-null
      def findPointers(p: PFormula, s: SFormula): Set[Expr] = {
        // All pointers
        val allPointers = (for (PointsTo(l, _, _) <- s.chunks) yield l).toSet
        allPointers.filter(
          { case x@Var(x_name) => !p.conjuncts.contains(x |/=| NilPtr) && !p.conjuncts.contains(NilPtr |/=| x) && notLvalVars.contains(x_name) }
        )
      }

      def addToAssertion(a: Assertion, ptrs: Set[Expr]): Assertion = {
        Assertion(a.phi && PFormula(ptrs.map { x => x |/=| NilPtr }), a.sigma)
      }

      val pre = goal.pre
      val post = goal.post

      val prePointers = findPointers(pre.phi, pre.sigma)
      val postPointers = findPointers(pre.phi && post.phi, post.sigma)

      if (prePointers.isEmpty && postPointers.isEmpty)
        Nil // no pointers to insert
      else {
        val newPre = addToAssertion(pre, prePointers)
        val newPost = addToAssertion(post, postPointers)
        val newGoal = goal.spawnChild(newPre, newPost)
        val kont = IdProducer >> ExtractHelper(goal)
        List(RuleResult(List(newGoal), kont, org.tygus.suslik.synthesis.rules.LogicalRules.NilNotLval, goal))
      }
    }


  }

  case class ReadGhost(ghostVar: String, intoVar: String, fromVar: String, offset: Int) extends SynthesisRule with FixedRules {
    override def nextRule: List[FixedRules] = List()
    def apply(goal: Goal): Seq[RuleResult] = {
      val phi = goal.pre.phi
      val sigma = goal.pre.sigma

      def selectedHeaplet: Heaplet => Boolean = {
        case PointsTo(x@Var(x_name), offs, e@Var(e_name)) => (x_name == fromVar && offs == offset && e_name == ghostVar)
        case _ => false
      }

      findHeaplet(selectedHeaplet, goal.pre.sigma) match {
        case None => Nil
        case Some(pts@PointsTo(x@Var(_), offset, e@Var(e_name))) =>
          val y = Var(intoVar)
          val tpy = e.getType(goal.gamma).get
          val newPhi = phi && (y |=| e)
          val newSigma = (sigma - pts) ** PointsTo(x, offset, y)
          val subGoal = goal.spawnChild(pre = Assertion(newPhi, newSigma),
            gamma = goal.gamma + (y -> tpy),
            programVars = y :: goal.programVars)
          val kont: StmtProducer = {
            SubstVarProducer(Var(e_name), y) >> PrependProducer(Load(y, tpy, x, offset)) >> ExtractHelper(goal)
          }
          List(RuleResult(List(subGoal), kont, org.tygus.suslik.synthesis.rules.OperationalRules.ReadRule, goal))
      }
    }

  }

  case class Frame(heaplets: List[Heaplet]) extends SynthesisRule with FixedRules {
    override def nextRule: List[FixedRules] = List()

    override def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post
      def selectedHeaplet(h:Heaplet) = {
        heaplets.exists(oh => h.eqModTags(oh))
      }
      def isMatch (hPre:Heaplet, hPost:Heaplet) =
        hPre.eqModTags(hPost) && selectedHeaplet(hPre)

      LogicalRules.findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
        case None => Nil
        case Some((hPre,hPost)) => {
          val newPreSigma = pre.sigma - hPre
          val newPostSigma = post.sigma - hPost
          val newPre = Assertion(pre.phi, newPreSigma)
          val newPost = Assertion(post.phi, newPostSigma)
          val newGoal = goal.spawnChild(newPre, newPost)
          val kont = IdProducer >> ExtractHelper(goal)
          List(RuleResult(List(newGoal), kont, org.tygus.suslik.synthesis.rules.LogicalRules.FrameFlat, goal))
        }
      }
    }

  }

  case class SubstL(fromVar: String, intoExpr: Expr) extends SynthesisRule with FixedRules {
    override def nextRule: List[FixedRules] = List()

    def apply(goal: Goal): Seq[RuleResult] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma

      // Should only substitute for a ghost
      def isGhostVar(e: Expr): Boolean = e.isInstanceOf[Var] && goal.universalGhosts.contains(e.asInstanceOf[Var])

      def extractSidesInternal(l: Expr, r: Expr): Option[(Var, Expr)] =
        if (l.vars.intersect(r.vars).isEmpty) {
          if (isGhostVar(l)) Some(l.asInstanceOf[Var], r)
          else if (isGhostVar(r)) Some(r.asInstanceOf[Var], l)
          else None
        } else None

      def extractSides(l:Expr, r:Expr) =
        extractSidesInternal(l,r).filter({case (Var(l), expr) => l==fromVar && expr == intoExpr})

      findConjunctAndRest({
        case BinaryExpr(OpEq, l, r) => extractSides(l, r)
        case BinaryExpr(OpBoolEq, l, r) => extractSides(l, r)
        case BinaryExpr(OpSetEq, l, r) => extractSides(l, r)
        case BinaryExpr(OpIntervalEq, l, r) => extractSides(l, r)
        case _ => None
      }, p1) match {
        case Some(((x, e), rest1)) => {
          val _p1 = rest1.subst(x, e)
          val _s1 = s1.subst(x, e)
          val newGoal = goal.spawnChild(Assertion(_p1, _s1), goal.post.subst(x, e))
          val kont = SubstProducer(x, e) >> IdProducer >> ExtractHelper(goal)
          assert(goal.callGoal.isEmpty)
          List(RuleResult(List(newGoal), kont, org.tygus.suslik.synthesis.rules.LogicalRules.SubstLeft, goal))
        }
        case _ => Nil
      }
    }
  }

  case object PrintGoal extends SynthesisRule with FixedRules {
    override def nextRule: List[FixedRules] = List()

    override def apply(goal: Goal) : Seq[RuleResult] = {
      println(s"${goal.pp}")
      throw SynthesisException("User called Halt")
    }
  }

  case class SubstR(fromVar: String, intoExpr: Expr) extends SynthesisRule with FixedRules {
    override def nextRule: List[FixedRules] = List()

    def apply(goal: Goal): Seq[RuleResult] = {
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      // Can e be substituted with d?
      def canSubst(e: Expr, d: Expr) = e match {
        case x@Var(_) =>
          // e must be an existential var:
          goal.isExistential(x) &&
            // if it's a program-level existential, then all vars in d must be program-level
            (!goal.isProgramLevelExistential(x) || d.vars.subsetOf(goal.programVars.toSet))
        case _ => false
      }

      def extractSidesInternal(l: Expr, r: Expr): Option[(Var, Expr)] =
        if (l.vars.intersect(r.vars).isEmpty) {
          if (canSubst(l, r)) Some(l.asInstanceOf[Var], r)
          else if (canSubst(r, l)) Some(r.asInstanceOf[Var], l)
          else None
        } else None

      def extractSides(l: Expr, r:Expr) =
        extractSidesInternal(l,r).filter({case (Var(l), r) => l == fromVar && r == intoExpr})

      findConjunctAndRest({
        case BinaryExpr(OpEq, l, r) => extractSides(l,r)
        case BinaryExpr(OpBoolEq, l, r) => extractSides(l,r)
        case BinaryExpr(OpSetEq, l, r) => extractSides(l,r)
        case BinaryExpr(OpIntervalEq, l, r) => extractSides(l,r)
        case _ => None
      }, p2) match {
        case Some(((x, e), rest2)) => {
          val sigma = Map(x -> e)
          val _p2 = rest2.subst(sigma)
          val _s2 = s2.subst(sigma)
          val newCallGoal = goal.callGoal.map(_.updateSubstitution(sigma))
          val newGoal = goal.spawnChild(post = Assertion(_p2, _s2), callGoal = newCallGoal)
          val kont = SubstProducer(x, e) >> IdProducer >> ExtractHelper(goal)
          List(RuleResult(List(newGoal), kont, org.tygus.suslik.synthesis.rules.UnificationRules.SubstRight, goal))
        }
        case _ => Nil
      }
    }
  }

  case class Write(intoVar:String, offset: Int, expr: Expr) extends SynthesisRule with FixedRules with SepLogicUtils {
    override def nextRule: List[FixedRules] = List()

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      def isSelectedPair(hfrom: Heaplet, hto: Heaplet) = {
        (hfrom,hto) match {
          case (PointsTo(Var(x), offs, _), PointsTo(Var(_), _, e)) => intoVar == x && offset == offs && e == expr
          case _ => false
        }
      }
      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && !sameRhs(hl)(hr) && noGhosts(hr) && isSelectedPair(hl,hr)

      OperationalRules.findMatchingHeaplets(_ => true, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@PointsTo(x@Var(_), offset, e1), hr@PointsTo(_, _, e2))) =>
          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi, goal.post.sigma - hr)
          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Store(x, offset, e2)) >> ExtractHelper(goal)

          List(RuleResult(List(subGoal), kont, org.tygus.suslik.synthesis.rules.OperationalRules.WriteRule, goal))
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }
  }

  case class CheckPost(validPost: PFormula) extends SynthesisRule with FixedRules {
    override def nextRule: List[FixedRules] = List()

    def filterOutValidPost(goal: Goal, exPost: PFormula, uniPost: PFormula): Seq[RuleResult] = {
      val validExConjuncts =
        exPost.conjuncts
          .filter(c => SMTSolving.valid(goal.pre.phi ==> c))
          .intersect(validPost.conjuncts)
      if (validExConjuncts.isEmpty && uniPost.conjuncts.isEmpty) Nil
      else {
        val newPost = Assertion(exPost - PFormula(validExConjuncts), goal.post.sigma)
        val newGoal = goal.spawnChild(post = newPost)
        List(RuleResult(List(newGoal),PureEntailmentProducer(goal.pre.phi, uniPost, goal.gamma) >> IdProducer, org.tygus.suslik.synthesis.rules.FailRules.CheckPost, goal))
      }
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val (uniPost, exPost) = goal.splitPost
      // If precondition does not contain predicates, we can't get new facts from anywhere
      if (!SMTSolving.valid(goal.pre.phi ==> uniPost))
      // universal post not implied by pre
        Nil // fail. used to be ...
        // List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal))
      else filterOutValidPost(goal, exPost, uniPost)
    }

  }

}
