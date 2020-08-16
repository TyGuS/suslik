package org.tygus.suslik.synthesis
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.{Block, Heaplet, PFormula, PointsTo, SApp, SFormula}
import org.tygus.suslik.logic.Specifications.Assertion

import scala.collection.immutable.{SortedSet, TreeSet}
object Evaluator {
  case class EvalResult(result: Assertion,
                        store: Map[Var, Expr]
                       )
  def evaluate(s: Statement, pre: Assertion): Assertion = {
    s match {
      case SeqComp(s1,s2)=> evaluate(s2, evaluate(s1,pre))
      case Load(to, _, from, offset) => {
        // to = b, from = x, offset = 1
        // lookup (from+offset) from Pre, giving PointsTo(x+1, v). (we know v = b, but doing this for completeness' sake)
        // then, want to replace every instance of (to = b) with (v = b).
        // do this by looking up "to" from Pre and replacing it with "v", giving PointsTo(to, _) :=> PointsTo(v, _)
        // PointsTo(_, to) :=> PointsTo(_, v); Block(to,_) :=> Block(v,_); Block(_, to) := Block(_,v)
        val curr = pre.sigma.chunks.collect{case PointsTo(loc, offset, value) => PointsTo(loc,offset,value)}.filter{
          case PointsTo(l,o,v) => from == l && offset == o
        }.head
        val curr_value = curr.value
        val new_sigma = pre.sigma.chunks.map{
          case PointsTo(l,o,v) => if (l == to) {
            PointsTo(curr_value,o,v)
          } else if (v == to) {
            PointsTo(l,o, curr_value)
          } else {PointsTo(l,o,v)}
          case Block(l,p) => if (l == to) {
            Block(curr_value,p)
          }
          case SApp(pred, args, tag, card) => {
            SApp(pred,args,tag,card)
          }
        }.asInstanceOf[List[Heaplet]]
        Assertion(new PFormula(TreeSet()), SFormula(new_sigma))
      }

      case _ => ???
    }
    Assertion(new PFormula(TreeSet()),SFormula(List()))
    //EvalResult(Assertion(new PFormula(TreeSet()),SFormula(List())), Map.empty[Var,Expr])
  }
}
