package org.tygus.synsl.logic

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language._

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
    phi.collectE(p) ++ sigma.collectE(p)

  def subst(s: Map[Var, Expr]): Assertion = Assertion(phi.subst(s), sigma.subst(s))

  // def |-(other: Assertion): Boolean = EntailmentSolver.entails(this, other)

  def refresh(bound: Set[Var]): (Assertion, Map[Var, Var]) = {
    val freshSubst = refreshVars(this.vars.toList, bound)
    (this.subst(freshSubst), freshSubst)
  }

  def bumpUpSAppTags(cond: Heaplet => Boolean = _ => true): Assertion =
    this.copy(sigma = this.sigma.bumpUpSAppTags(cond))

  def lockSAppTags(cond: Heaplet => Boolean = _ => true): Assertion =
    this.copy(sigma = this.sigma.lockSAppTags(cond))

}

case class RuleAppMetadata(rule: String, timestamp: (Int, Int), footprint: (Set[Int], Set[Int]))

case class Derivation(preIndex: List[Heaplet], postIndex: List[Heaplet], applications: List[RuleAppMetadata] = Nil) {
}

/**
  * Main class for contextual Hoare-style specifications
  */
case class Goal(pre: Assertion, post: Assertion, gamma: Gamma, fname: String, deriv: Derivation)
  extends PrettyPrinting with PureLogicUtils {

  override def pp: String =
    s"${gamma.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")} |-\n" +
      s"${pre.pp}\n${post.pp}"

  def simpl: Goal = copy(Assertion(simplify(pre.phi), pre.sigma),
    Assertion(simplify(post.phi), post.sigma))
  

  def hasAllocatedBlocks: Boolean = pre.sigma.chunks.exists(_.isInstanceOf[Block])

  /**
    * How many unfoldings can we tolerate
    */
  def closeCredit: Int = post.sigma.chunks.map{
    case SApp(_, _, Some(i)) => i
    case _ => 0
  }.sum

  def vars: Set[Var] = pre.vars ++ post.vars ++ gamma.map(_._2)

  def formals: Set[Var] = gamma.map(_._2).toSet

  def ghosts: Set[Var] = pre.vars ++ post.vars -- formals

  def universals: Set[Var] = pre.vars ++ formals

  def existentials: Set[Var] = post.vars -- universals

  def givenConstants: Set[Const] = pre.collectE(_.isInstanceOf[Const])

  def constantsInPost: Set[Const] = post.collectE(_.isInstanceOf[Const])

  // Determine whether `x` is a ghost variable wrt. given spec and gamma
  def isGhost(x: Var): Boolean = ghosts.contains(x)

  // Determine whether x is in the context
  def isConcrete(x: Var): Boolean = gamma.map(_._2).contains(x)

  def isExistential(x: Var): Boolean = existentials.contains(x)

  def getType(x: Var): SynslType = {
    // TODO: all ghosts are void for now; we treat void as the top type
    gamma.find(_._2 == x) match {
      case Some((t, _)) => t
      case None => VoidType
    }
    /*
    if (isGhost(x)) {
      // Deduce the type from the parameter types and the spec
      val candidates = pre.sigma.findSubFormula {
        case PointsTo(_, _, v) => v == x
        case _ => false
      }
      if (candidates.isEmpty) return None
      val PointsTo(y, _, _) = candidates.head

      val assocType: Option[(SynslType, Var)] = gamma.find(pv => pv._2.name == y.name)
      if (assocType.isEmpty) return None
      return assocType.get._1 match {
        case PtrType(inner) => Some(inner)
        case _ => None
      }
    } else {
      // Typed variables get the type automatically
      gamma.find(_._2 == x) match {
        case Some((t, _)) => Some(t)
        case None => None
      }
    }
    */
  }

}
