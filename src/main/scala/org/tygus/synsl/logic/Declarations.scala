package org.tygus.synsl.logic

import org.tygus.synsl.PrettyPrinting
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.SynslType
import org.tygus.synsl.logic.Specifications._

/**
  * @author Ilya Sergey
  */

object Declarations {

  /**
    * A top-level declaration in a program
    */
  sealed abstract class Declaration extends PrettyPrinting {

  }

  /**
    * Function to synthesize
    *
    * @param name function name
    * @param spec pre/postconditions and variable context
    * @param tpe  function return type
    */
  case class GoalFunction(name: Ident, spec: Spec, tpe: SynslType) extends Declaration {
    override def pp: String = {
      val Spec(pre, post, gamma) = spec
      s"${pre.pp}\n${tpe.pp} " +
        s"$name(${gamma.map { case (t, i) => s"${t.pp} ${i.pp}" }.mkString(", ")})\n" +
        s"${post.pp}"
    }

  }

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
    * predicate lseg(x, y) {
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
  case class InductiveDef(name: Ident, params: Seq[Var], clauses: Seq[InductiveClause]) extends Declaration {

    override def pp : String = {
      val prelude = s"predicate $name (${params.map(_.pp).mkString(", ")}) { \n  "
      val cls = clauses.map(_.pp).mkString("\n| ")
      prelude + cls + "\n}"
    }

    // TODO: implement me
    def existentials: Set[Var] = ???

  }

  case class Program(decls: Seq[Declaration]) extends PrettyPrinting {
    override def pp: String = decls.map(_.pp).mkString("\n\n")
  }

}
