package org.tygus.synsl.logic

import org.tygus.synsl.language._
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.SynslType

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
  extends TopLevelDeclaration {

  override def pp: String = {
    val prelude = s"$name (${params.map(_.pp).mkString(", ")}) {"
    val cls = clauses.map(_.pp).mkString(" | ")
    prelude + cls + "}"
  }

  def valid: Boolean = clauses.forall(_.valid)

  // TODO: implement me
  def existentials: Set[Var] = ???

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
case class Environment(predicates: PredicateEnv, functions: FunctionEnv, unfoldingsLeft: Int) {
  def pp: String = {
    val ps = predicates.values.toSet.toList.map((x: InductivePredicate) => x.pp).mkString("; ")
    val psStr = if (ps.nonEmpty) s"[Predicates (${predicates.size}): $ps]" else ""
    val fs = functions.values.toSet.toList.map((x: FunSpec) => x.ppInline).mkString("; ")
    val fsStr = if (functions.nonEmpty) s"\n[Functions  (${functions.size}): $fs]" else ""
    //val post = if (ps.nonEmpty || fs.nonEmpty) "\n" else ""
    s"$psStr$fsStr"
  }
}

