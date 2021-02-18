package org.tygus.suslik.certification.targets.iris.logic

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HBinOp, HExpr, HOpEq, HOpLe, HOpLt}
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HLocType, HType}
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.language.Statements.Procedure

object Assertions {

  /** Unlike HTT, which encodes programs in a shallow embedding, Iris has a deep embedding of programs.
    *  As such, program expressions are NOT Iris assertions (phi != HExpr). We define a lifting of
    *  program-level expressions to spec-level. */
  abstract class HSpecExpr extends PrettyPrinting

  case class HSpecVar(name: String) extends HSpecExpr {
    override def pp: String = s"${name}"
  }

  case class HSpecBinaryExpr(op: HBinOp, left: HSpecExpr, right: HSpecExpr) extends HSpecExpr {
    override def pp: String = op match {
      case HOpLe | HOpLt | HOpEq => s"bool_decide (${left.pp} ${op.pp} ${right.pp})%Z"
      case _ => ???
    }
  }

  abstract class IPureAssertion extends PrettyPrinting
  abstract class ISpatialAssertion extends PrettyPrinting

  abstract class ISpecification extends PrettyPrinting

  case class IPointsTo(loc: HExpr, value: HExpr) extends ISpatialAssertion {
    override def pp: String = s"${loc.pp} ↦ ${value.pp}"
  }

  case class IHeap(heaplets: Seq[ISpatialAssertion]) extends ISpatialAssertion {
    override def pp: String = s"${heaplets.map(_.pp).mkString(" ∗ ")}"
  }

  case class IFunSpec(proc: Procedure,
                      funArgs: Seq[(HSpecVar, HType)],
                      specUniversal: Seq[HSpecVar],
                      specExistential: Seq[HSpecVar],
                      pre: ISpatialAssertion,
                      post: ISpatialAssertion
                     ) extends ISpecification {

    override def pp: String = {
      def getArgLitVal(v : HSpecVar, t: HType) : HSpecVar =
      (v, t) match {
          case (HSpecVar(name), HLocType()) => HSpecVar(s"l${name}")
          case (HSpecVar(name), _) => HSpecVar(s"v${name}")
        }

      val var_at = (v:HSpecVar, t: HType) => s"${t.pp}_at ${v.pp} ${getArgLitVal(v, t).pp}"
      val postExist =
        if (specExistential.nonEmpty)
          s"∃ ${specExistential.map(v => v.pp).mkString("  ")}"
        else ""

      s"""
         |Lemma ${proc.name}_spec :
         |∀ ${specUniversal.map(v => v.pp).mkString(" ")},
         |${funArgs.map(v => var_at(v._1, v._2)).mkString(" →\n")} →
         |{{{ ${pre.pp} }}}
         |  ${proc.name} ${funArgs.map(v => v._1.pp).mkString(" ")}
         |{{{ RET #(); ${postExist}, ${post.pp} }}}.
         |""".stripMargin
    }
  }

}