package org.tygus.suslik.logic

import org.tygus.suslik.language.Expressions.{BinaryExpr, Expr, OpEq, OpLt}
import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.synthesis.SynConfig

object Preprocessor extends SepLogicUtils {

  /**
    * Collect program declarations into an environment
    * TODO: type checking
    */
  def preprocessProgram(prog: Program): (Seq[FunSpec], Environment, Statement) = {
    val Program(preds, funs, goal) = prog
    val funMap = funs.map(fs => fs.name -> fs).toMap

    // [Cardinality] Instrument predicates with missing cardinality constraints
    // val newPreds = preds

    // Enable predicate instrumentation
    val newPreds = preds.map(p => p.copy(clauses = p.clauses.map(addCardConstraintsClause)))
    
    val predMap = newPreds.map(ps => ps.name -> ps).toMap
    (List(goal.spec), Environment(predMap, funMap, SynConfig()), goal.body)
  }

  /**
    * Add a missing cardinality constraint to a predicate clause 
    */
  private def addCardConstraintsClause(clause: InductiveClause): InductiveClause = {
    val InductiveClause(sel, Assertion(phi, sigma)) = clause

    // All cardinality-related variables
    val cardVars = (for {
      SApp(_, _, _, card) <- sigma.chunks
      v <- card.vars
    } yield v).toSet
    
    
    // Constant footprint
    if (cardVars.isEmpty) {
      val (_, clauseCard) = heapCardinality(sigma)
      val cardConstraint = BinaryExpr(OpEq, selfCardVar, clauseCard) // self_card = x
      val newPhi = PFormula(phi.conjuncts ++ Set(cardConstraint))
      return InductiveClause(sel, Assertion(newPhi, sigma))
    }

    val constrainedVars = sel.vars ++ phi.vars
    if (cardVars.subsetOf(constrainedVars)) return clause // No constraints to add

    // Otherwise, generate for the clause cardinality
    val (ptsCount, clauseCard) = heapCardinality(sigma)

    // Main equality
    val cardConstraint = BinaryExpr(OpEq, selfCardVar, clauseCard) // self_card = 2 + _alpha_xxx

    // To help the solver with strict inequalities - needed for trees
    val additionalConstraints: Set[Expr] =
      if (ptsCount == 0) Set.empty
      else for {
        v <- cardVars
      } yield BinaryExpr(OpLt, v, selfCardVar)


    val newPhi = PFormula(phi.conjuncts ++ Set(cardConstraint) ++ additionalConstraints)

    InductiveClause(sel, Assertion(newPhi, sigma))
  }


}
