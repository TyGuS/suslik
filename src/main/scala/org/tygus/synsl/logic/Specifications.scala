package org.tygus.synsl.logic

import org.tygus.synsl.LanguageUtils
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language._
import org.tygus.synsl.synthesis.SynthesisRule

import scala.math.Ordering.Implicits._

object Specifications {

  case class Assertion(phi: PFormula, sigma: SFormula) extends Substitutable[Assertion]
    with PureLogicUtils {

    def pp: String = s"{${phi.pp} ; ${sigma.pp}}"

    // Get free variables
    def varsPhi: Set[Var] = phi.vars

    def varsSigma: Set[Var] = sigma.collectE(_.isInstanceOf[Var])

    // Get all variables in the assertion
    def vars: Set[Var] = varsPhi ++ varsSigma

    // Collect arbitrary expressions
    def collectE[R <: Expr](p: Expr => Boolean): Set[R] =
      phi.collect(p) ++ sigma.collectE(p)

    def hasPredicates: Boolean = sigma.chunks.exists(_.isInstanceOf[SApp])

    def subst(s: Map[Var, Expr]): Assertion = Assertion(phi.subst(s), sigma.subst(s))

    def refresh(bound: Set[Var]): (Assertion, SubstVar) = {
      val freshSubst = refreshVars(this.vars.toList, bound)
      (this.subst(freshSubst), freshSubst)
    }

    /**
      * For all pointers x :-> v, changes v to a fresh variable $ex.
      * Returns a substitution from $ex to v.
      */
    def relaxPTSImages: (Assertion, Subst) = {
      val ptss = sigma.ptss
      val (_, sub, newPtss) =
        ptss.foldRight((Set.empty: Set[Var], Map.empty: Subst, Nil: List[PointsTo])) {
          case (p@PointsTo(x, off, e), z@(taken, sbst, acc)) =>
            // Only relax if the pure part is not affected!
            if (e.vars.intersect(phi.vars).isEmpty) {
              val freshName = LanguageUtils.generateFreshExistential(taken)
              val taken1 = taken + freshName
              val sub1 = sbst + (freshName -> e)
              (taken1, sub1, PointsTo(x, off, freshName) :: acc)
            } else (taken, sbst, p :: acc)
        }
      val newSigma = SFormula(sigma.chunks.filter(!ptss.contains(_)) ++ newPtss)
      (this.copy(sigma = newSigma), sub)
    }

    def bumpUpSAppTags(cond: Heaplet => Boolean = _ => true): Assertion =
      this.copy(sigma = this.sigma.bumpUpSAppTags(cond))

    def lockSAppTags(cond: Heaplet => Boolean = _ => true): Assertion =
      this.copy(sigma = this.sigma.lockSAppTags(cond))

    def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
      for {
        gamma1 <- phi.resolve(gamma, Some(BoolType))
        gamma2 <- sigma.resolve(gamma1, env)
      } yield gamma2
    }

    // TODO: take into account distance between pure parts
    def distance(other: Assertion): Int = this.sigma.distance(other.sigma)

  }

  case class RuleApplication(rule: SynthesisRule, footprint: (Set[Int], Set[Int]), timestamp: (Int, Int))
    extends PrettyPrinting with Ordered[RuleApplication] {
    override def pp: String =
      s"${this.rule} ${this.timestamp} ${this.footprint}"

    // Does this rule application commute with a previous application prev?
    // Yes if my footprint only includes chunks that existed before prev was applied
    def commutesWith(prev: RuleApplication): Boolean = {
      this.footprint._1.forall(i => i < prev.timestamp._1) &&
        this.footprint._2.forall(i => i < prev.timestamp._2)
    }

    // Rule applications are ordered by their footprint
    // (the actual order doesn't really matter, as long as not all rules are equal)
    override def compare(that: RuleApplication): Int = {
      val min1 = this.footprint._1.union(this.footprint._2).min
      val min2 = that.footprint._1.union(that.footprint._2).min
      min1.compare(min2)
    }
  }


  case class Derivation(preIndex: List[Heaplet], postIndex: List[Heaplet], applications: List[RuleApplication] = Nil)
    extends PrettyPrinting {
    override def pp: String =
      s"${preIndex.length}: [ ${preIndex.map(_.pp).mkString(" , ")} ]" +
        s"\n${postIndex.length}: [ ${postIndex.map(_.pp).mkString(" , ")} ]" +
        s"\nRules: ${applications.map(_.pp).mkString(" , ")}"

    // Find a previous rule application that is out of order with the latest one
    def outOfOrder(ruleOrder: Seq[SynthesisRule]): Option[RuleApplication] = {

      // app1 is ordered before app2
      // if its rule comes earlier in the rule order,
      // or the rules are the same and the footprint comes earlier
      def before(app1: RuleApplication, app2: RuleApplication): Boolean = {
        val i1 = ruleOrder.indexOf(app1.rule)
        val i2 = ruleOrder.indexOf(app2.rule)
        (i1, app1) < (i2, app2)
      }

      applications match {
        case Nil => None
        case latest :: prevs => prevs.find(prev => latest.commutesWith(prev) && before(latest, prev))
      }
    }
  }

  /**
    * Main class for contextual Hoare-style specifications
    */
  case class Goal(pre: Assertion,
                  post: Assertion,
                  gamma: Gamma,
                  programVars: List[Var],
                  fname: String,
                  env: Environment,
                  deriv: Derivation)
    extends PrettyPrinting with PureLogicUtils {

    override def pp: String =
      s"${programVars.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")} |-\n" +
        s"${pre.pp}\n${post.pp}" // + s"\n${deriv.pp}"

    def simpl: Goal = copy(Assertion(simplify(pre.phi), pre.sigma),
      Assertion(simplify(post.phi), post.sigma))

    def copy(pre: Assertion = this.pre,
             post: Assertion = this.post,
             gamma: Gamma = this.gamma,
             programVars: List[Var] = this.programVars,
             env: Environment = this.env,
             newRuleApp: Option[RuleApplication] = None): Goal = {

      // Variables that used to be universals but would become existentials
      val fauxExistentials: Set[Var] = (post.vars -- (pre.vars ++ programVars) -- this.existentials) intersect this.vars
      val conjuncts: List[PFormula] = for (v <- fauxExistentials.toList) yield v.eq(v, getType(v))
      // For each such variable, add a trivial euqality to the pure precondition to avoid changing the meaning
      val preAdjusted = pre.copy(phi = mkConjunction(pre.phi :: conjuncts))

      // Resolve types
      val gammaFinal = resolvePrePost(gamma, env, preAdjusted, post)

      // Build a new derivation
      def appendNewChunks(oldAsn: Assertion, newAsn: Assertion, index: List[Heaplet]): List[Heaplet] = {
        index ++ newAsn.sigma.chunks.diff(oldAsn.sigma.chunks).sortBy(_.rank)
      }
      val d = this.deriv
      val newDeriv = d.copy(preIndex = appendNewChunks(this.pre, preAdjusted, d.preIndex),
        postIndex = appendNewChunks(this.post, post, d.postIndex),
        applications = newRuleApp.toList ++ d.applications)

      // Sort heaplets from old to new
      val newPreSigma = pre.sigma.copy(pre.sigma.chunks.sortBy(h => newDeriv.preIndex.lastIndexOf(h)))
      val newPostSigma = post.sigma.copy(post.sigma.chunks.sortBy(h => newDeriv.postIndex.lastIndexOf(h)))
      val preSorted = preAdjusted.copy(sigma = newPreSigma)
      val postSorted = post.copy(sigma = newPostSigma)

      Goal(preSorted, postSorted, gammaFinal, programVars, this.fname, env, newDeriv)
    }

    def hasAllocatedBlocks: Boolean = pre.sigma.chunks.exists(_.isInstanceOf[Block])

    def hasPredicates: Boolean = pre.hasPredicates || post.hasPredicates

    // All variables this goal has ever used
    def vars: Set[Var] = deriv.preIndex.flatMap(_.vars).toSet ++ deriv.postIndex.flatMap(_.vars).toSet ++ programVars

    // Variables currently used only in specs
    def ghosts: Set[Var] = pre.vars ++ post.vars -- programVars

    // Universally quantified variables: program variables and ghosts in pre
    def universals: Set[Var] = programVars.toSet ++ pre.vars

    // Ghosts that appear only in the postcondition
    def existentials: Set[Var] = post.vars -- universals

    // Determine whether `x` is a ghost variable wrt. given spec and gamma
    def isGhost(x: Var): Boolean = ghosts.contains(x)

    // Determine whether x is in the context
    def isProgramVar(x: Var): Boolean = programVars.contains(x)

    def isExistential(x: Var): Boolean = existentials.contains(x)

    def addProgramVar(v: Var, t: SynslType): Goal =
      this.copy(gamma = this.gamma + (v -> t), programVars = v :: this.programVars)

    def getType(x: Var): SynslType = {
      gamma.get(x) match {
        case Some(t) => t
        case None => VoidType
      }
    }

    def formals: Formals = programVars.map(v => (getType(v), v))

    def distance: Int = pre.distance(post)

  }

  private def resolvePrePost(gamma0: Gamma, env: Environment, pre: Assertion, post: Assertion): Gamma = {
    pre.resolve(gamma0, env) match {
      case None => throw SepLogicException(s"Resolution error in specification: ${pre.pp}")
      case Some(gamma1) => post.resolve(gamma1, env) match {
        case None => throw SepLogicException(s"Resolution error in specification: ${post.pp}")
        case Some(gamma) => gamma
      }
    }
  }

  def makeNewGoal(pre: Assertion, post: Assertion, formals: Formals, fname: String, env: Environment): Goal = {
    val gamma0 = formals.map({ case (t, v) => (v, t) }).toMap // initial environemnt: derived fromn the formals
    val gamma = resolvePrePost(gamma0, env, pre, post)
    val formalNames = formals.map(_._2)
    val emptyDerivation = Derivation(pre.sigma.chunks, post.sigma.chunks)
    Goal(pre, post, gamma, formalNames, fname, env, emptyDerivation)
  }
}
