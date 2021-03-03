package org.tygus.suslik.logic

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.synthesis.SynConfig

import scala.collection.immutable.Set

object Preprocessor extends SepLogicUtils {

  /**
    * Collect program declarations into an environment
    * TODO: type checking
    */
  def preprocessProgram(prog: Program, params: SynConfig): (Seq[FunSpec], PredicateEnv, FunctionEnv, Statement) = {
    val Program(preds, funs, goal) = prog
    val funMap = funs.map(fs => fs.name -> fs).toMap

    // [Cardinality] Instrument predicates with missing cardinality constraints
    // val newPreds = preds

    // Enable predicate instrumentation
    val newPreds = preds.map(p => p.copy(clauses = p.clauses.map(addCardConstraints)))

    val predMap = newPreds.map(ps => ps.name -> ps).toMap
    (List(goal.spec), predMap, funMap, goal.body)
  }

  /**
    * Add a missing cardinality constraint to a predicate clause 
    */
  private def addCardConstraints(clause: InductiveClause): InductiveClause = {
    val InductiveClause(sel, Assertion(phi, sigma)) = clause

    // All cardinality-related variables
    val cardVars = (for {
      SApp(_, _, _, card) <- sigma.chunks
      v <- card.vars
    } yield v).toSet

    val constrainedVars = sel.vars ++ phi.vars
    if (cardVars.subsetOf(constrainedVars)) return clause // No constraints to add

    // Otherwise, generate for the clause cardinality
    val (ptsCount, clauseCard) = heapCardinality(sigma)

    // Inequalities

    // All cardinalities are less than self-cardinality
    val ltCards = if (ptsCount > 0) {
      for (cv <- cardVars) yield BinaryExpr(OpLt, cv, selfCardVar)
    } else Set.empty
    
    val newPhi = PFormula(phi.conjuncts ++ ltCards)

    InductiveClause(sel, Assertion(newPhi, sigma))
  }

}
