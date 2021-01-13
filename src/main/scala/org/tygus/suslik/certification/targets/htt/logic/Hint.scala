package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.Expressions.CVar
import org.tygus.suslik.certification.targets.htt.language.Types.CNatSeqType
import org.tygus.suslik.certification.targets.htt.logic.Sentences.CInductivePredicate

object Hint {
  abstract class Item {
    val dbName: String
    def pp: String
    def ppResolve(ident: String): String = s"Hint Resolve $ident: $dbName"
  }

  case class PredicateSetTransitive(pred: CInductivePredicate) extends Item {
    val name: String = s"${pred.name}_perm_eq_trans"
    val dbName: String = "ssl_pred"
    def pp: String = {
      val items = pred.params.zipWithIndex.filter(_._1._1 == CNatSeqType).map { case ((tp, v), i) =>
        val (before, after) = pred.params.map(_._2).splitAt(i)
        val s1 = CVar("s1")
        val s2 = CVar("s2")
        val params1 = before ++ Seq(s1) ++ after.tail
        val params2 = before ++ Seq(s2) ++ after.tail
        val args = before ++ after.tail ++ Seq(s1, s2)
        val hyp = s"Hypothesis $name$i: forall ${args.map(_.pp).mkString(" ")}, perm_eq ${s1.pp} ${s2.pp} -> ${pred.name} ${params1.map(_.pp).mkString(" ")} -> ${pred.name} ${params2.map(_.pp).mkString(" ")}"
        val resolve = ppResolve(s"$name$i")
        s"$hyp.\n$resolve"
      }
      assert(items.nonEmpty, "can't generate hypothesis for predicate with no seq nat parameters")
      s"${items.mkString(".\n")}."
    }
  }
}
