package org.tygus.synsl.logic

import org.tygus.synsl.PrettyPrinting
import org.tygus.synsl.language.Expressions._

/**
  * @author Ilya Sergey
  */

trait InductivePredicates {
  this: SpatialFormulas =>

  /*
  A selector is of the form (phi, sigma)
   */
  case class InductiveClause(selector: PFormula, body: SFormula) extends PrettyPrinting {
    override def pp: String =
      s"${selector.pp} => ${body.pp}"
  }

  /**
    * An inductive definition has a name and a collection of clauses.
    *
    * For instance, a linked list can be encoded as follows:
    *
    * lseg(x, y) {
    *    x == y  =>  emp
    *  | x != y  => x -> (V, Z) * lseg(Z, y)
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
  case class InductiveDef(name: Ident, params: Seq[Var], clauses: Seq[InductiveClause]) extends PrettyPrinting {

    override def pp : String = {
      val prelude = s"$name (${params.map(_.pp).mkString(", ")}) { \n  "
      val cls = clauses.map(_.pp).mkString("\n| ")
      prelude + cls + "\n}"
    }

    // TODO: implement me
    def existentials: Set[Var] = ???

  }
}
