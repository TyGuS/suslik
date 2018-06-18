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

case class RuleApplication(rule: String, footprint: (Set[Int], Set[Int]), timestamp: (Int, Int))
  extends PrettyPrinting with Ordered[RuleApplication]
{
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


case class Derivation(preIndex: List[SFormula], postIndex: List[SFormula], applications: List[RuleApplication] = Nil)
  extends PrettyPrinting
{
  override def pp: String =
      s"${preIndex.length}: [ ${preIndex.map(_.pp).mkString(" , ")} ]" +
        s"\n${postIndex.length}: [ ${postIndex.map(_.pp).mkString(" , ")} ]" +
        s"\nRules: ${applications.map(_.pp).mkString(" , ")}"

  // Find a previous rule application that is out of order with the latest one
  def outOfOrder: Option[RuleApplication] = {
    applications match {
      case Nil => None
      case latest :: prevs => prevs.find(prev => latest.commutesWith(prev) && latest < prev)
    }
  }
}

/**
  * Main class for contextual Hoare-style specifications
  */
case class Goal(pre: Assertion, post: Assertion, gamma: Gamma, fname: String, deriv: Derivation)
  extends PrettyPrinting with PureLogicUtils {

  override def pp: String =
    s"${gamma.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")} |-\n" +
      s"${pre.pp}\n${post.pp}" +
      s"\n${deriv.pp}"

  def simpl: Goal = copy(Assertion(simplify(pre.phi), pre.sigma),
    Assertion(simplify(post.phi), post.sigma))

  def copy(pre: Assertion = this.pre,
           post: Assertion = this.post,
           gamma: Gamma = this.gamma,
           newRuleApp: Option[RuleApplication] = None): Goal = {

    def appendNewChunks(oldAsn: Assertion, newAsn: Assertion, index:List[SFormula]): List[SFormula] = {
      index ++ newAsn.sigma.chunks.diff(oldAsn.sigma.chunks)
    }

    val mapper = (hs: List[Heaplet]) => hs.map(h => SFormula(List(h)))

    val d = this.deriv
    val newDeriv = d.copy(preIndex = mapper(appendNewChunks(this.pre, pre, d.preIndex)),
      postIndex = mapper(appendNewChunks(this.post, post, d.postIndex)),
      applications = newRuleApp.toList ++ d.applications)
    Goal(pre,post,gamma,this.fname,newDeriv)
  }


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
