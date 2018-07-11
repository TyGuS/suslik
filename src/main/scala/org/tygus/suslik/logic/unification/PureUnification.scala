package org.tygus.suslik.logic.unification

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.PureLogicUtils

/**
  * Unification based on pure parts
  *
  * @author Ilya Sergey
  */

object PureUnification extends PureLogicUtils {

  def tryUnify(target: Expr, source: Expr, freeVars: Set[Var]): Seq[Subst] = {
    // assert(target.vars.forall(nonFreeInSource.contains), s"Not all variables of ${target.pp} are in $nonFreeInSource")
    (source, target) match {
      case (x@Var(_), e) if freeVars.contains(x) => {
        List(Map(x -> e))
      }
      case (UnaryExpr(op1, s), UnaryExpr(op2, t))
        if op1 == op2 =>
        tryUnify(t, s, freeVars)
      case (BinaryExpr(op1, ls, rs), BinaryExpr(op2, lt, rt))
        if op1 == op2 && op1.isInstanceOf[SymmetricOp] =>
        val m1 = unifyPairs(lt, rt, ls, rs, freeVars)
        val m2 = unifyPairs(rt, lt, ls, rs, freeVars)
        m1 ++ m2
      case (BinaryExpr(op1, ls, rs), BinaryExpr(op2, lt, rt)) if op1 == op2 =>
        unifyPairs(lt, rt, ls, rs, freeVars)
      // TODO: allow permutations
      case (SetLiteral(Nil), SetLiteral(Nil)) => List(Map.empty)
      case (SetLiteral(es :: ess), SetLiteral(et :: ets)) =>
        unifyPairs( et, SetLiteral(ets), es, SetLiteral(ess), freeVars)
      case _ => if (source == target) List(Map.empty) else Nil
    }
  }

  
  private def unifyPairs(lt: Expr, rt: Expr, ls: Expr, rs: Expr, freeVars: Set[Var]): Seq[Subst] =
    for {
      m1 <- tryUnify(lt, ls, freeVars)
      m2 <- tryUnify(rt.subst(m1), rs.subst(m1), freeVars)
    } yield m1 ++ m2
}
