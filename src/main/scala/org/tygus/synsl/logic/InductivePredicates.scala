package org.tygus.synsl.logic

import org.tygus.synsl.language.Expressions._

/**
  * @author Ilya Sergey
  */

trait InductivePredicates {
  this: SpatialFormulas =>

  /*
  A selector is of the form (phi, sigma)
   */
  case class InductiveClause(selector: PFormula, body: SFormula)

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
    * Each clause condition does not contain free variables, only the parameters,
    * while all free variables in the spatial part (body) is existentially quantified.
    *
    * Also add simple predicate definitions
    *
    * TODO: add higher-order predicates, e.g., a list parameterised by a predicate
    *
    */
  case class InductiveDef(name: Ident, params: Seq[Var], clauses: Seq[InductiveClause]) {

    // TODO: implement me
    def existentials: Set[Var] = ???

  }
}
