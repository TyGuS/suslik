package org.tygus.synsl.logic.unification

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.logic.unification.PureUnification.unifyPairs
import org.tygus.synsl.logic.{PFormula, SEq}

/**
  * Unification based on pure parts
  *
  * @author Ilya Sergey
  */

object PureUnification extends UnificationBase {
  type UAtom = PFormula

  val needRefreshing: Boolean = false
  val precise: Boolean = false


  protected def extractChunks(goal: UnificationGoal): List[PFormula] = {
    conjuncts(goal.formula.phi).distinct.filter(_.isInstanceOf[SEq])
  }

  protected def checkShapesMatch(cs1: List[PFormula], cs2: List[PFormula]): Boolean = {
    val (seqs1, seqs2) = (cs1.filter(_.isInstanceOf[SEq]), cs2.filter(_.isInstanceOf[SEq]))
    !(seqs1.isEmpty || seqs2.isEmpty)
  }

  def tryUnify(target: PFormula, source: PFormula, nonFreeInSource: Set[Var]): Seq[Subst] = {
    assert(target.vars.forall(nonFreeInSource.contains), s"Not all variables of ${target.pp} are in $nonFreeInSource")
    (source, target) match {
      case (SEq(ls, rs), SEq(lt, rt)) =>
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
    case (x@Var(_), e) => {
      genSubst(e, x, nonFreeInSource).toList
    }
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
