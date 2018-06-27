package org.tygus.synsl.logic.unification

import org.tygus.synsl.language.Expressions._

/**
  * Unification based on pure parts
  *
  * @author Ilya Sergey
  */

object PureUnification extends UnificationBase {
  type UAtom = PFormula

  val needRefreshing: Boolean = false
  val precise: Boolean = false

  private def isSetEq(e: Expr): Boolean = e match {
    case BinaryExpr(OpSetEq, _, _) => true
    case _ => false
  }

  protected def extractChunks(goal: UnificationGoal): List[PFormula] = {
    conjuncts(goal.formula.phi).distinct.filter(isSetEq)
  }

  protected def checkShapesMatch(cs1: List[PFormula], cs2: List[PFormula]): Boolean = {
    val (seqs1, seqs2) = (cs1.filter(isSetEq), cs2.filter(isSetEq))
    !(seqs1.isEmpty || seqs2.isEmpty)
  }

  def tryUnify(target: PFormula, source: PFormula, nonFreeInSource: Set[Var]): Seq[Subst] = {
    assert(target.vars.forall(nonFreeInSource.contains), s"Not all variables of ${target.pp} are in $nonFreeInSource")
    (source, target) match {
      case (BinaryExpr(OpSetEq, ls, rs), BinaryExpr(OpSetEq, lt, rt)) =>
        val m1 = unifyPairs(ls, rs, lt, rt, nonFreeInSource)
        val m2 = unifyPairs(ls, rs, rt, lt, nonFreeInSource)
        m1 ++ m2
      case _ => Nil
    }
  }

  
  private def unifyPairs(ls: Expr, rs: Expr, lt: Expr, rt: Expr, nonFreeInSource: Set[Var]): Seq[Subst] =
    for {
      m1 <- unifyAsSetExpr(ls, lt, nonFreeInSource)
      m2 <- unifyAsSetExpr(rs, rt, nonFreeInSource)
      if agreeOnSameKeys(m1, m2)
    } yield m1 ++ m2


  private def unifyAsSetExpr(s: Expr, t: Expr, nonFreeInSource: Set[Var]): Seq[Subst] = (s, t) match {
    case (x@Var(_), e) =>
      genSubst(e, x, nonFreeInSource).toList
    case (BinaryExpr(OpUnion, ls, rs), BinaryExpr(OpUnion, lt, rt)) =>
      val m1 = unifyPairs(ls, rs, lt, rt, nonFreeInSource)
      val m2 = unifyPairs(ls, rs, rt, lt, nonFreeInSource)
      m1 ++ m2
    case (SetLiteral(Nil), SetLiteral(Nil)) => List(Map.empty)
    case (SetLiteral(es :: Nil), SetLiteral(et :: Nil)) =>
      unifyAsSetExpr(es, et, nonFreeInSource)
      // TODO: these are not sets, and also take care of non-singleton cases
    case _ => List(Map.empty)
  }

}
