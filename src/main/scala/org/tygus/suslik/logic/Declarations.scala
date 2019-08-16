package org.tygus.suslik.logic

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.language.SSLType
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis._

/**
  * @author Ilya Sergey
  */

/**
  * A top-level declaration in a program
  */
sealed abstract class TopLevelDeclaration extends PrettyPrinting with PureLogicUtils

/**
  * Function to synthesize
  *
  * @param name  function name
  * @param rType function return type
  */
case class FunSpec(name: Ident, rType: SSLType, params: Formals,
                   pre: Assertion, post: Assertion) extends TopLevelDeclaration {

  def resolveOverloading(env:Environment):FunSpec = {
    val gamma0 = params.map({ case (t, v) => (v, t) }).toMap // initial environemnt: derived fromn the formals
    val gamma = resolvePrePost(gamma0, env, pre, post)
    this.copy(pre=pre.resolveOverloading(gamma), post=post.resolveOverloading(gamma))
  }

  override def pp: String = {
    s"${pre.pp}\n${rType.pp} " +
        s"$name(${params.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")})\n" +
        s"${post.pp}"
  }


  def ppInline: String = {
    s"${rType.pp} " +
        s"$name(${params.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")})" +
        s" ${pre.pp} ${post.pp}"
  }

  def relaxFunSpec = {
    val (relaxedPre, sub) = pre.relaxPTSImages
    val reversedSub = for ((k, v@Var(_)) <- sub) yield v -> k
    val relaxedPost = post.subst(reversedSub)
    (this.copy(pre = relaxedPre, post = relaxedPost), sub)
  }

  def refreshExistentials(taken: Set[Var]): FunSpec = {
    val sub = refreshVars(((post.vars -- pre.vars) -- params.map(_._2).toSet).toList, taken)
    val newPre = pre.subst(sub)
    val newPost = post.subst(sub)
    this.copy(pre = newPre, post = newPost)
  }

  def checkVariableMutabilityTags(): Unit = {
    assert (post.mutabilityVariables.subsetOf(pre.mutabilityVariables))
  }

}

/**
  * A selector is of the form (phi, sigma)
  */
case class InductiveClause(selector: PFormula, asn: Assertion) extends PrettyPrinting with PureLogicUtils {
  override def pp: String =
    s"${selector.pp} => ${asn.pp}"

  def valid: Boolean = isAtomicPFormula(selector)

  /*
    Get info about types
  * result:
  * None: contradiction in resolve
  * Some(gamma, true): new info obtained
  * Some(gamma, false): no new info
  * */
  def resolve(gamma0: Gamma, env: Environment):Option[Gamma]= {
    val new_gamma = for {
      gamma1 <- selector.resolve(gamma0, Some(BoolType))
      gamma2 <- asn.resolve(gamma1, env)
    }yield gamma2
    if(new_gamma.isEmpty){
      None
    }else{
      if (!new_gamma.contains(gamma0)){ // Info was updated, so it worth to make a new iteration
        resolve(new_gamma.get, env)
      }else{
        new_gamma // No update, return
      }
    }
  }

  def resolveOverloading(gamma: Gamma): InductiveClause ={
    this.copy(selector = selector.resolveOverloading(gamma), asn=asn.resolveOverloading(gamma))
  }
}

/**
  * An inductive definition has a name and a collection of clauses.
  *
  * For instance, a linked list can be encoded as follows:
  *
  * predicate lseg(x, y) {
  * x == y  =>  emp
  * | x != y  => x -> (V, Z) * lseg(Z, y)
  * }
  *
  *
  * Each clause condition does not contain free variables, only the parameters,
  * while all free variables in the spatial part (body) is existentially quantified.
  *
  * Also add simple predicate definitions
  *
  * TODO: add higher-order predicates, e.g., a list parameterised by a predicate
  *
  */
case class InductivePredicate(name: Ident, params: Formals, clauses: Seq[InductiveClause])
    extends TopLevelDeclaration with PureLogicUtils {

  def resolve(gamma: Gamma, env:Environment):Option[Gamma] = {
    val init_gamma : Option[Gamma] = Some(gamma)
    val new_gamma = clauses.foldLeft(init_gamma)((accum_gamma, clause) => accum_gamma match{
      case Some(g) => clause.resolve(g, env)
      case _ => None
    })
    new_gamma match {
      case Some(g) =>
        if (g == gamma) Some(g) else resolve(g, env)
      case _ => None
    }
  }

  def resolveOverloading(env:Environment): InductivePredicate = {
    val gamma0 = params.map({ case (t, v) => (v, t) }).toMap // initial environemnt: derived from the params
    val gamma = resolve(gamma0, env)
    if (gamma.isEmpty) throw SepLogicException(s"Resolution error in predicate: ${this.pp}")
    this.copy(clauses = clauses.map(_.resolveOverloading(gamma.get)))
  }

  override def pp: String = {
    val prelude = s"$name (${params.map(_._2.pp).mkString(", ")}) {"
    val cls = clauses.map(_.pp).mkString(" | ")
    prelude + cls + "}"
  }

  def valid: Boolean = clauses.forall(_.valid)

  /**
    * Renames existentials so they wouldn't capture the parameters and `vars`
    *
    * @param vars additional contextual variables that can be captures
    * @return inductive predicate
    */
  def refreshExistentials(vars: Set[Var]): InductivePredicate = {
    val bound = vars ++ params.map(_._2).toSet
    val sbst = refreshVars(existentials.toList, bound)
    this.copy(clauses = this.clauses.map(c => InductiveClause(c.selector.subst(sbst), c.asn.subst(sbst))))
  }

  def vars: Set[Var] = clauses.flatMap(c => c.selector.vars ++ c.asn.vars).toSet

  def existentials: Set[Var] = vars -- params.map(_._2).toSet

}

/**
  * Program: for now just a sequence of declarations
  */
case class Program(predicates: Seq[InductivePredicate],
                   funs: Seq[FunSpec],
                   goal: FunSpec) extends PrettyPrinting {
  override def pp: String = predicates.map(_.pp).mkString("\n\n") ++ funs.map(_.pp).mkString("\n\n")
}


/**
  * Environment: stores module-level declarations that might be needed during synthesis
  * (predicates, component functions, etc)
  */
case class Environment(predicates: PredicateEnv, functions: FunctionEnv,
                       config: SynConfig = defaultConfig,
                       startTime: Long) {
  def pp: String = {
    val ps = predicates.values.toSet.toList.map((x: InductivePredicate) => x.pp).mkString("; ")
    val psStr = if (ps.nonEmpty) s"[Predicates (${predicates.size}): $ps]" else ""
    val fs = functions.values.toSet.toList.map((x: FunSpec) => x.ppInline).mkString("; ")
    val fsStr = if (functions.nonEmpty) s"\n[Functions  (${functions.size}): $fs]" else ""
    //val post = if (ps.nonEmpty || fs.nonEmpty) "\n" else ""
    s"$psStr$fsStr"
  }

  def resolveOverloading(): Environment = { // No gamma in input, because every fun & pred has own gamma
    this.copy(predicates = predicates.map{case (k,v) => (k, v.resolveOverloading(this))},
      functions=functions.map{case (k,v) => (k, v.resolveOverloading(this))})
  }
}

