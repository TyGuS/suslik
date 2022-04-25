package org.tygus.suslik.logic

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.language.SSLType
import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.util.SynStats

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
  * @param params function parameters names and types
  * @param pre precondition
  * @param post post-condition
  * @param var_decl local variable of function?
  */
case class FunSpec(name: Ident, rType: SSLType, params: Formals,
                   pre: Assertion, post: Assertion,
                   var_decl: Formals = Nil) extends TopLevelDeclaration {

  def resolveOverloading(env: Environment): FunSpec = {
    val gamma0 = params.toMap // initial environment: derived from the formals
    val gamma = resolvePrePost(gamma0, env, pre, post)
    this.copy(pre = pre.resolveOverloading(gamma), post = post.resolveOverloading(gamma))
  }

  def gamma(env: Environment): Gamma = {
    val gamma0 = params.toMap // initial environment: derived from the formals
    val gamma = resolvePrePost(gamma0, env, pre, post)
    gamma
  }

  def existentials() : List[Var] = {
    val params = this.params.map(_._1).toSet
    val formal_params = pre.ghosts(params)
    val existentials = post.ghosts(formal_params ++ params)
    existentials.toList
  }

  // Currently used universally qualtified variables: program variables and ghosts in pre
  def universals : Set[Var] = pre.vars ++ this.params.map(v => v._1)

  override def pp: String = {
    (""
      + s"${rType.pp} "
      + s"$name(${params.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}) "
      + s"[${var_decl.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")}]\n"
      + s"${pre.pp}\n"
      + s"${post.pp}"
      )
  }


  def ppInline: String = {
    s"${rType.pp} " +
        s"$name(${params.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")})" +
        s" ${pre.pp} ${post.pp}"
  }

  def refreshAll(taken: Set[Var], suffix: String = ""): (SubstVar, FunSpec) = {
    val sub = refreshVars((post.vars ++ pre.vars ++ params.map(_._1).toSet).toList, taken, suffix)
    val newParams = params.map({case (v, t) => (v.varSubst(sub), t)})
    val newVarDecl = var_decl.map({case (v, t) => (v.varSubst(sub), t)})
    val newPre = pre.subst(sub)
    val newPost = post.subst(sub)
    (sub, this.copy(params = newParams, pre = newPre, post = newPost, var_decl = newVarDecl))
  }

  def varSubst(sigma: SubstVar): FunSpec = this.copy(
    params = this.params.map({ case (v, t) => (v.varSubst(sigma), t)}),
    pre = this.pre.subst(sigma),
    post = this.post.subst(sigma))

  def substUnknown(sigma: UnknownSubst): FunSpec = this.copy(
    pre = this.pre.copy(this.pre.phi.substUnknown(sigma), this.pre.sigma),
    post = this.post.copy(this.post.phi.substUnknown(sigma), this.post.sigma)
  )
}

/**
  * A selector is of the form (phi, sigma)
  */
case class InductiveClause(selector: Expr, asn: Assertion) extends PrettyPrinting with PureLogicUtils {
  override def pp: String =
    s"${selector.pp} => ${asn.pp}"

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
    this.copy(selector = selector.resolveOverloading(gamma), asn = asn.resolveOverloading(gamma))
  }
}

/**
  * An inductive definition has a name and a collection of clauses.
  *
  * For instance, a linked list can be encoded as follows:
  *
  * predicate lseg(x, y)[α] {
  * x == y  =>  emp
  * | x != y  => x -> (V, Z) * lseg(Z, y)
  * }
  *
  *
  * Each clause condition does not contain free variables, only the parameters,
  * while all free variables in the spatial part (body) is existentially quantified.
  * 
  * α is an identifier that stands for predicate cardinality and is necessary for the cyclic proof checking.
  * In case if it's missing from the definition, it's instantiated with predname_card
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
    val gamma0 = params.toMap // initial environemnt: derived from the params
    val gamma = resolve(gamma0, env)
    if (gamma.isEmpty) throw SepLogicException(s"Resolution error in predicate: ${this.pp}")
    this.copy(clauses = clauses.map(_.resolveOverloading(gamma.get)))
  }

  override def pp: String = {
    val prelude = s"$name (${params.map(_._2.pp).mkString(", ")})"
    // Print cardinality parameter
    val cls = clauses.map(_.pp).mkString(" | ")
    prelude  + s"{ $cls }"
  }

  /**
    * Renames existentials so they wouldn't capture the parameters and `vars`
    *
    * @param vars additional contextual variables that can be captures
    * @return inductive predicate and substitution used
    */
  def refreshExistentials(vars: Set[Var], suffix: String = ""): (InductivePredicate, SubstVar) = {
    val bound = Set(selfCardVar) ++ vars ++ params.map(_._1).toSet
    val sbst = refreshVars(existentials.toList, bound, suffix)
    (this.copy(clauses = this.clauses.map(c => InductiveClause(c.selector.subst(sbst), c.asn.subst(sbst)))), sbst)
  }

  def vars: Set[Var] = clauses.flatMap(c => c.selector.vars ++ c.asn.vars).toSet

  def existentials: Set[Var] = vars -- params.map(_._1).toSet -- Set(selfCardVar)

}


case class GoalContainer(spec: FunSpec, body: Statement)

/**
  * Program: for now just a sequence of declarations
  */
case class Program(predicates: Seq[InductivePredicate],
                   funs: Seq[FunSpec],
                   goal: GoalContainer) extends PrettyPrinting {
  override def pp: String = predicates.map(_.pp).mkString("\n\n") ++ funs.map(_.pp).mkString("\n\n")
}



/**
  * Environment: stores module-level declarations that might be needed during synthesis
  * (predicates, component functions, etc)
  */
case class Environment(predicates: PredicateEnv,
                       functions: FunctionEnv,
                       config: SynConfig,
                       stats: SynStats) {
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

