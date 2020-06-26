package org.tygus.suslik.logic

import org.tygus.suslik.LanguageUtils
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._
import Ordering.Implicits._

object Specifications extends SepLogicUtils {

  case class Assertion(phi: PFormula, sigma: SFormula) extends HasExpressions[Assertion]
    with PureLogicUtils {

    def pp: String = if (phi.conjuncts.isEmpty) s"{${sigma.pp}}" else s"{${phi.pp} ; ${sigma.pp}}"

    // Collect arbitrary expressions
    def collect[R <: Expr](p: Expr => Boolean): Set[R] =
      phi.collect(p) ++ sigma.collect(p)

    def hasPredicates: Boolean = sigma.chunks.exists(_.isInstanceOf[SApp])

    def getPredicates(p: SApp => Boolean): List[SApp] =
      for (s@SApp(_, _, _, _) <- sigma.chunks if p(s)) yield s

    def hasBlocks: Boolean = sigma.chunks.exists(_.isInstanceOf[Block])

    // Difference between two assertions
    def -(other: Assertion): Assertion = Assertion(PFormula(phi.conjuncts -- other.phi.conjuncts), sigma - other.sigma)

    def subst(s: Map[Var, Expr]): Assertion = Assertion(phi.subst(s), sigma.subst(s))

    /**
      * @param takenNames  -- names that are already taken
      * @param globalNames -- variables that shouldn't be renamed
      * @return
      */
    def refresh(takenNames: Set[Var], globalNames: Set[Var]): (Assertion, SubstVar) = {
      val varsToRename = (vars -- globalNames).toList
      val freshSubst = refreshVars(varsToRename, takenNames ++ globalNames)
      (this.subst(freshSubst), freshSubst)
    }

    def ghosts(params: Set[Var]): Set[Var] = this.vars -- params

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
      val newSigma = mkSFormula(sigma.chunks.filter(!ptss.contains(_)) ++ newPtss)
      (this.copy(sigma = newSigma), sub)
    }

    def bumpUpSAppTags(cond: Heaplet => Boolean = _ => true): Assertion =
      this.copy(sigma = this.sigma.bumpUpSAppTags(cond))

    def lockSAppTags(cond: Heaplet => Boolean = _ => true): Assertion =
      this.copy(sigma = this.sigma.lockSAppTags(cond))

    def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
      for {
        gamma1 <- phi.resolve(gamma)
        gamma2 <- sigma.resolve(gamma1, env)
      } yield gamma2
    }

    def resolveOverloading(gamma: Gamma): Assertion = {
      this.copy(phi = toFormula(simplify(phi.toExpr.resolveOverloading(gamma))),
        sigma = sigma.resolveOverloading(gamma))
    }

    // TODO: take into account distance between pure parts
    def similarity(other: Assertion): Int = this.sigma.similarity(other.sigma)

    // Size of the assertion (in AST nodes)
    def size: Int = phi.size + sigma.size

    def cost: Int = sigma.cost
  }

  /**
    * Spatial pre-post pair; used to determine independence of rule applications.
    */
  case class Footprint(pre: Assertion, post: Assertion) {
    def -(other: Footprint): Footprint = Footprint(pre - other.pre, post - other.post)
  }

  /**
    * A label uniquely identifies a goal within a derivation tree (but not among alternative derivations!)
    * Here depths represents how deep we should go down a linear segment of a derivation tree
    * and children represents which branch to take at each fork.
    * For example, a label ([2, 1], [0]) means go 2 steps down from the root, take 0-th child, then go 1 more step down.
    * This label is pretty-printed as "2-0.1"
    */
  case class GoalLabel(depths: List[Int], children: List[Int]) extends PrettyPrinting with Ordered[GoalLabel]  {
    override def pp: String = {
      val d :: ds = depths.reverse
      d.toString ++ children.reverse.zip(ds).map(x => "-" + x._1.toString + "." + x._2.toString).mkString
    }

    private def toList: List[Int] = (List(depths.head) ++ children.zip(depths.tail).flatMap {case (i, j) => List(i, j)}).reverse

    def compare(that: GoalLabel): Int = implicitly[Ordering[List[Int]]].compare(toList, that.toList)

    def bumpUp(childId: Option[Int]): GoalLabel = {
      childId match {
        case None => {
          // Derivation is not branching: simply increase the latest depth
          val x :: xs = depths
          this.copy(depths = (x + 1) :: xs)
        }
        case Some(c) =>
          // Derivation is branching: record which branch we are taking and reset depth
          GoalLabel(0 :: depths, c :: children)
      }
    }
  }

  /**
    * Main class for contextual Hoare-style specifications
    */
  case class Goal(pre: Assertion,
                  post: Assertion,
                  gamma: Gamma, // types of all variables (program, universal, and existential)
                  programVars: List[Var], // program-level variables
                  universalGhosts: Set[Var], // universally quantified ghost variables
                  fname: String, // top-level function name
                  label: GoalLabel, // unique id within the derivation
                  parent: Option[Goal], // parent goal in the derivation
                  env: Environment, // predicates and components
                  sketch: Statement, // sketch
                  callGoal: Option[SuspendedCallGoal],
                  preNormalized: Boolean, // TODO: this ugliness is here to optimize SubstleftVar / SubstRightVar
                  postNormalized: Boolean,
                 )

    extends PrettyPrinting with PureLogicUtils {

    override def pp: String =
//      s"${label.pp}\n" +
      s"${programVars.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")} " +
        s"[${universalGhosts.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")}]" +
        s"[${existentials.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")}] |-\n" +
        s"${pre.pp}\n${sketch.pp}${post.pp}"

    lazy val splitPost: (PFormula, PFormula) = {
      val (ex, uni) = post.phi.conjuncts.partition(p => p.vars.exists(this.isExistential))
      (PFormula(uni), PFormula(ex))
    }

    def universalPost: PFormula = splitPost._1

    // Ancestors of this goal in the derivation (root last)
    lazy val ancestors: List[Goal] = parent match {
      case None => Nil
      case Some(p) => p :: p.ancestors
    }

    def ancestorWithLabel(l: GoalLabel): Option[Goal] = ancestors.find(_.label == l)

    // Ancestors before progress was last made
    def companionCandidates: List[Goal] = {
      ancestors.dropWhile(_.label.depths.length == this.label.depths.length).filter(_.callGoal.isEmpty)
      // TODO: actually sufficient to consider everything before last open
    }

    // Turn this goal into a helper function specification
    def toFunSpec: FunSpec = {
      val name = this.fname + this.label.pp.replaceAll("[^A-Za-z0-9]", "").tail
      val varDecl = this.ghosts.toList.map(v => (v, getType(v))) // Also remember types for non-program vars
      FunSpec(name, VoidType, this.formals, this.pre, this.post, varDecl)
    }

    // Turn this goal into a helper function call
    def toCall: Statement = {
      val f = this.toFunSpec
      Call(Var(f.name), f.params.map(_._1), None)
    }

    def toFootprint: Footprint = Footprint(pre, post)

    def spawnChild(pre: Assertion = this.pre,
                   post: Assertion = this.post,
                   gamma: Gamma = this.gamma,
                   programVars: List[Var] = this.programVars,
                   childId: Option[Int] = None,
                   env: Environment = this.env,
                   sketch: Statement = this.sketch,
                   callGoal: Option[SuspendedCallGoal] = this.callGoal,
                   preNormalized: Boolean = false,
                   postNormalized: Boolean = false): Goal = {

      // Resolve types
      val gammaFinal = resolvePrePost(gamma, env, pre, post)

      // Sort heaplets from old to new and simplify pure parts
      val preSimple = Assertion(simplify(pre.phi), pre.sigma)
      val postSimple = Assertion(simplify(post.phi), post.sigma)
//      val usedVars = preSimple.vars ++ postSimple.vars ++ programVars.toSet
//      val newGamma = gammaFinal.filterKeys(usedVars.contains)
//      val newUniversalGhosts = this.universalGhosts.intersect(usedVars) ++ preSimple.vars -- programVars
      val newUniversalGhosts = this.universalGhosts ++ preSimple.vars -- programVars

      Goal(preSimple, postSimple,
        gammaFinal, programVars, newUniversalGhosts,
        this.fname, this.label.bumpUp(childId), Some(this), env, sketch,
        callGoal,
        preNormalized, postNormalized)
    }

    // Goal that is eagerly recognized by the search as unsolvable
    def unsolvableChild: Goal = spawnChild(post = Assertion(pFalse, emp))

    // Is this goal unsolvable and should be discarded?
    def isUnsolvable: Boolean = post.phi == pFalse

    def isTopLevel: Boolean = label == topLabel

    def getPredicates(p: SApp => Boolean): Seq[SApp] = pre.getPredicates(p) ++ post.getPredicates(p)

    def hasPredicates(p: SApp => Boolean = _ => true): Boolean = getPredicates(p).nonEmpty

    def hasBlocks: Boolean = pre.hasBlocks || post.hasBlocks

    def hasExistentialPointers: Boolean = post.sigma.chunks.exists {
      case PointsTo(x@Var(_), _, _) => isExistential(x)
      case _ => false
    }

    // All variables this goal has ever used
    def vars: Set[Var] = gamma.keySet

    // All universally-quantified variables this goal has ever used
    def allUniversals: Set[Var] = universalGhosts ++ programVars

    // Variables currently used only in specs
    def ghosts: Set[Var] = pre.vars ++ post.vars -- programVars

    // Currently used universally quantified variables: program variables and ghosts in pre
    def universals: Set[Var] = pre.vars ++ programVars

    // Currently used ghosts that appear only in the postcondition
    def existentials: Set[Var] = post.vars -- allUniversals

    // Determine whether `x` is a ghost variable wrt. given spec and gamma
    def isGhost(x: Var): Boolean = ghosts.contains(x)

    // Determine whether x is in the context
    def isProgramVar(x: Var): Boolean = programVars.contains(x)

    def isExistential(x: Var): Boolean = existentials.contains(x)

    def getType(x: Var): SSLType = {
      gamma.get(x) match {
        case Some(t) => t
        case None => VoidType
      }
    }

    def formals: Formals = programVars.map(v => (v, getType(v)))

    def depth: Int = ancestors.length

    def similarity: Int = pre.similarity(post)

    // Size of the specification in this goal (in AST nodes)
    def specSize: Int = pre.size + post.size

    /**
      * Cost of a goal:
      * for now just the number of heaplets in pre and post
      */
    //    lazy val cost: Int = pre.cost.max(post.cost)
    lazy val cost: Int = pre.cost + post.cost
  }

  def resolvePrePost(gamma0: Gamma, env: Environment, pre: Assertion, post: Assertion): Gamma = {
    pre.resolve(gamma0, env) match {
      case None => throw SepLogicException(s"Resolution error in specification: ${pre.pp}")
      case Some(gamma1) => post.resolve(gamma1, env) match {
        case None => throw SepLogicException(s"Resolution error in specification: ${post.pp}")
        case Some(gamma) => gamma
      }
    }
  }

  // Label of the top-level goal
  def topLabel: GoalLabel = GoalLabel(List(0), List())

  def topLevelGoal(pre: Assertion, post: Assertion, formals: Formals, fname: String, env: Environment, sketch: Statement, vars_decl: Formals): Goal = {
    val gamma0 = (formals ++ vars_decl).toMap // initial environemnt: derived from the formals
    val gamma = resolvePrePost(gamma0, env, pre, post)
    val pre1 = pre.resolveOverloading(gamma)
    val post1 = post.resolveOverloading(gamma)
    val formalNames = formals.map(_._1)
    val ghostUniversals = pre1.vars -- formalNames
    Goal(pre1, post1,
      gamma, formalNames, ghostUniversals,
      fname, topLabel, None, env.resolveOverloading(), sketch.resolveOverloading(gamma), None, false, false)
  }

  /**
    * Stored information necessary to compute call arguments and the goal after call
    * when in call abduction mode
    * @param callerPre precondition of the goal where call abduction started
    * @param callerPost postcondition of the goal where call abduction started
    * @param calleePost postcondiiton of the companion goal
    * @param call call statement
    */
  case class SuspendedCallGoal(callerPre: Assertion,
                               callerPost: Assertion,
                               calleePost: Assertion,
                               call: Call,
                               companionToFresh: SubstVar,
                               freshToActual: Subst = Map.empty) {
    def updateSubstitution(sigma: Subst): SuspendedCallGoal = {
      assertNoOverlap(freshToActual, sigma)
      this.copy(freshToActual = compose(freshToActual, sigma) ++ sigma)
    }

    def actualCall: Call = call.copy(args = call.args.map(_.subst(freshToActual)))
  }
}


