package org.tygus.suslik.logic

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._

import scala.Ordering.Implicits._

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
                  hasProgressed: Boolean,
                  isCompanion: Boolean
                 )

    extends PrettyPrinting with PureLogicUtils {

    override def pp: String = {
      def postWithCall: String = {
        val actualCG = callGoal.get.applySubstitution
        s"${post.pp.init} ** ...}\n${actualCG.call.pp}${actualCG.calleePost.pp.init} ** ...}\n...\n${actualCG.callerPost.pp}"
      }

//      s"${label.pp}\n" +
      s"${programVars.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")} " +
        s"[${universalGhosts.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")}]" +
        s"[${existentials.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")}] |-\n" +
        s"${pre.pp}\n${sketch.pp}" +
        (if (callGoal.isEmpty) post.pp else postWithCall)
    }

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

    // Companion candidates for this goal:
    // look at ancestors before progress was last made, only keep those with different heap profiles
    def companionCandidates: List[Goal] = {
      val allCands = ancestors.dropWhile(!_.hasProgressed).drop(1).filter(_.isCompanion).reverse
      if (env.config.auxAbduction) allCands else allCands.take(1)
  }

    // Turn this goal into a helper function specification
    def toFunSpec: FunSpec = {
      val name = this.fname + this.label.pp.replaceAll("[^A-Za-z0-9]", "").tail
      val varDecl = this.ghosts.toList.map(v => (v, getType(v))) // Also remember types for non-program vars
      FunSpec(name, VoidType, this.formals, this.pre, this.post, varDecl)
    }

    // Turn this goal into a helper function call
    def toCall: Call = {
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
                   hasProgressed: Boolean = false,
                   isCompanion: Boolean = false): Goal = {

      // Resolve types
      val gammaFinal = resolvePrePost(gamma, env, pre, post)

      // Sort heaplets from old to new and simplify pure parts
      val preSimple = Assertion(simplify(pre.phi), pre.sigma)
      val postSimple = Assertion(simplify(post.phi), post.sigma)
//      val usedVars = preSimple.vars ++ postSimple.vars ++ programVars.toSet ++
//        callGoal.map(cg => cg.calleePost.vars ++ cg.callerPost.vars).getOrElse(Set())
//      val newGamma = gammaFinal.filterKeys(usedVars.contains)
//      val newUniversalGhosts = this.universalGhosts.intersect(usedVars) ++ preSimple.vars -- programVars
      val newUniversalGhosts = this.universalGhosts ++ preSimple.vars -- programVars

      Goal(preSimple, postSimple,
        gammaFinal, programVars, newUniversalGhosts,
        this.fname, this.label.bumpUp(childId), Some(this), env, sketch,
        callGoal, hasProgressed, isCompanion)
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

    // Currently used ghosts that appear only in the postcondition
    def existentials: Set[Var] = post.vars -- allUniversals

    // Determine whether `x` is a ghost variable wrt. given spec and gamma
    def isGhost(x: Var): Boolean = ghosts.contains(x)

    // Determine whether x is in the context
    def isProgramVar(x: Var): Boolean = programVars.contains(x)

    def isExistential(x: Var): Boolean = existentials.contains(x)

    def progLevelPrefix: String = "_prog_"

    // Is x an argument to the call being adbuced
    // and thus must only be unified with program-level expressions?
    def isProgramLevelExistential(x:Var): Boolean = x.name.startsWith(progLevelPrefix) || (
      callGoal match {
        case None => false
        case Some(cg) => cg.call.args.contains(x)
      })

    def getType(x: Var): SSLType = {
      gamma.get(x) match {
        case Some(t) => t
        case None => VoidType
      }
    }

    def substToFormula(sigma: ExprSubst): PFormula = {
      PFormula(sigma.map{ case (e1,e2) => e1 |===| e2}.toSet).resolveOverloading(gamma)
    }

    def splitSubst(sigma: ExprSubst): (Subst, PFormula) = {
      sigma.partition{ case (e, _) => e.isInstanceOf[Var] && isExistential(e.asInstanceOf[Var]) } match {
        case (sub, exprSub) => (sub.map { case (v, e) => (v.asInstanceOf[Var], e)}, substToFormula(exprSub))
      }
    }

    def formals: Formals = programVars.map(v => (v, getType(v)))

    def depth: Int = ancestors.length

    // Size of the specification in this goal (in AST nodes)
    def specSize: Int = pre.size + post.size

    /**
      * Cost of a goal:
      * for now just the number of heaplets in pre and post
      */
    //    lazy val cost: Int = pre.cost.max(post.cost)
    lazy val cost: Int = callGoal match {
        case None => 3*pre.cost + post.cost  // + existentials.size //
        case Some(cg) => 10 + 3*cg.callerPre.cost + cg.callerPost.cost // + (cg.callerPost.vars -- allUniversals).size //
      }
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

  def topLevelGoal(funSpec: FunSpec, env: Environment, sketch: Statement): Goal = {
    val FunSpec(name, _, formals, pre, post, var_decl) = funSpec
    topLevelGoal(pre, post, formals, name, env, sketch, var_decl)
  }

  def topLevelGoal(pre: Assertion, post: Assertion, formals: Formals, fname: String, env: Environment, sketch: Statement, vars_decl: Formals): Goal = {
    val gamma0 = (formals ++ vars_decl).toMap // initial environemnt: derived from the formals
    val gamma = resolvePrePost(gamma0, env, pre, post)
    val pre1 = pre.resolveOverloading(gamma)
    val post1 = post.resolveOverloading(gamma)
    val formalNames = formals.map(_._1)
    val ghostUniversals = pre1.vars -- formalNames
    Goal(pre1, post1,
      gamma, formalNames, ghostUniversals,
      fname, topLabel, None, env.resolveOverloading(), sketch.resolveOverloading(gamma),
      None, hasProgressed = false, isCompanion = true)
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

    def applySubstitution: SuspendedCallGoal = {
      val newCalleePost = calleePost.subst(freshToActual)
      val newCall = call.copy(args = call.args.map(_.subst(freshToActual)))
      this.copy(calleePost = newCalleePost, call = newCall)
    }

    def actualCall: Call = call.copy(args = call.args.map(_.subst(freshToActual)))

    lazy val cost: Int = calleePost.cost
  }
}


