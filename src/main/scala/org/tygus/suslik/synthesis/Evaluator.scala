package org.tygus.suslik.synthesis
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.{PFormula, SFormula}
import org.tygus.suslik.logic.Specifications.Assertion

import scala.collection.immutable.{SortedSet, TreeSet}
object Evaluator {
  case class EvalResult(result: Assertion,
                        store: Map[Var, Expr]
                       )
  def evaluate(s: Statement): EvalResult = {
    EvalResult(Assertion(new PFormula(TreeSet()),SFormula(List())), Map.empty[Var,Expr])
  }
}
