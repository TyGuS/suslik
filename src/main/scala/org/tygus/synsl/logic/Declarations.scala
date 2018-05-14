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
  * @param name function name
  * @param goal pre/postconditions and variable context
  * @param tpe  function return type
  */
case class GoalFunction(name: Ident, goal: Goal, tpe: SynslType) extends TopLevelDeclaration {
  override def pp: String = {
    val Goal(pre, post, gamma) = goal
    s"${pre.pp}\n${tpe.pp} " +
        s"$name(${gamma.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")})\n" +
        s"${post.pp}"
  }

}

/**
  * A selector is of the form (phi, sigma)
  */
case class InductiveClause(selector: PFormula, body: SFormula) extends PrettyPrinting with PureLogicUtils {
  override def pp: String =
    s"${selector.pp} => ${body.pp}"

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
case class InductivePredicate(name: Ident, params: Seq[Var], clauses: Seq[InductiveClause]) extends TopLevelDeclaration {

  override def pp: String = {
    val prelude = s"predicate $name (${params.map(_.pp).mkString(", ")}) { \n  "
    val cls = clauses.map(_.pp).mkString("\n| ")
    prelude + cls + "\n}"
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
case class Environment(predicates: PredIndex)

