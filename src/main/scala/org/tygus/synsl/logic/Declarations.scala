package org.tygus.synsl.logic

import org.tygus.synsl.language._
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.SynslType
import org.tygus.synsl.synthesis.rules.UnfoldingRules.ApplyHypothesisAbduceFrameRule.refreshVars

/**
  * @author Ilya Sergey
  */

/**
  * A top-level declaration in a program
  */
sealed abstract class TopLevelDeclaration extends PrettyPrinting

/**
  * Function to synthesize
  *
  * @param name  function name
  * @param rType function return type
  */
case class FunSpec(name: Ident, rType: SynslType, params: Gamma,
                   pre: Assertion, post: Assertion) extends TopLevelDeclaration {
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


}

/**
  * A selector is of the form (phi, sigma)
  */
case class InductiveClause(selector: PFormula, asn: Assertion) extends PrettyPrinting with PureLogicUtils {
  override def pp: String =
    s"${selector.pp} => ${asn.pp}"

  def valid: Boolean = isAtomicPFormula(selector)

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
case class InductivePredicate(name: Ident, params: Seq[Var], clauses: Seq[InductiveClause])
  extends TopLevelDeclaration with PureLogicUtils {

  override def pp: String = {
    val prelude = s"$name (${params.map(_.pp).mkString(", ")}) {"
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
    val bound = vars ++ params.toSet
    val sbst = refreshVars(existentials.toList, bound)
    this.copy(clauses = this.clauses.map(c => InductiveClause(c.selector.subst(sbst), c.asn.subst(sbst))))
  }

  def vars: Set[Var] = clauses.flatMap(c => c.selector.vars ++ c.asn.vars).toSet

  def existentials: Set[Var] = vars -- params.toSet

}

/**
  * Program: for now just a sequence of declarations
  */
case class Program(decls: Seq[TopLevelDeclaration]) extends PrettyPrinting {
  override def pp: String = decls.map(_.pp).mkString("\n\n")
}


/**
  * Environment: stores module-level declarations that might be needed during synthesis
  * (predicates, component functions, etc)
  */
case class Environment(predicates: PredicateEnv, functions: FunctionEnv,
                       unfoldingsLeft: Int = 1) {
  def pp: String = {
    val ps = predicates.values.toSet.toList.map((x: InductivePredicate) => x.pp).mkString("; ")
    val psStr = if (ps.nonEmpty) s"[Predicates (${predicates.size}): $ps]" else ""
    val fs = functions.values.toSet.toList.map((x: FunSpec) => x.ppInline).mkString("; ")
    val fsStr = if (functions.nonEmpty) s"\n[Functions  (${functions.size}): $fs]" else ""
    //val post = if (ps.nonEmpty || fs.nonEmpty) "\n" else ""
    s"$psStr$fsStr"
  }
}

