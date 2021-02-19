package org.tygus.suslik.certification.targets.iris.logic

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.{HBinOp, HLit, HOpEq, HOpLe, HOpLt}
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HLocType, HType}
import org.tygus.suslik.language.PrettyPrinting

object Assertions {

  /** Unlike HTT, which encodes programs in a shallow embedding, Iris has a deep embedding of programs.
    *  As such, program expressions are NOT Iris assertions (phi != HExpr). We define a lifting of
    *  program-level expressions to spec-level. */
  abstract class IPureAssertion extends PrettyPrinting {
    def ppAsPhi: String = pp
  }
  abstract class IQuantifiedVar extends IPureAssertion

  case class ISpecLit(lit: HLit) extends IPureAssertion {
    override def pp: String = lit.pp
  }

  case class ISpecVar(name: String) extends IQuantifiedVar {
    override def pp: String = s"${name}"
  }

  case class ISpecQuantifiedValue(name: String) extends IQuantifiedVar {
    override def pp: String = s"${name}"
  }

  case class ISpecBinaryExpr(op: HBinOp, left: IPureAssertion, right: IPureAssertion) extends IPureAssertion {
    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"

    override def ppAsPhi: String = op match {
      case HOpLe | HOpLt | HOpEq => s"bool_decide (${left.pp} ${op.pp} ${right.pp})%Z"
      case _ => ???
    }
  }

  abstract class ISpatialAssertion extends PrettyPrinting

  case class IAnd(conjuncts: Seq[IPureAssertion]) extends IPureAssertion {
    override def pp: String = s"${conjuncts.map(_.ppAsPhi).mkString(" ∧ ")}"
  }

  case class IPointsTo(loc: IPureAssertion, value: IPureAssertion) extends ISpatialAssertion {
    override def pp: String = s"${loc.pp} ↦ ${value.pp}"
  }

  case class IHeap(heaplets: Seq[ISpatialAssertion]) extends ISpatialAssertion {
    override def pp: String = s"${heaplets.map(_.pp).mkString(" ∗ ")}"
  }

  case class IAssertion(phi: IPureAssertion, sigma: ISpatialAssertion) extends PrettyPrinting {
    override def pp: String = {
      val pure = if (phi.ppAsPhi.isEmpty) "" else s"⌜${phi.ppAsPhi}⌝ ∗ "
      val whole = s"${pure}${sigma.pp}"
      if (whole.isEmpty) "True" else whole
    }
  }

  abstract class ISpecification extends PrettyPrinting

  case class IFunSpec(fname: String,
                      funArgs: Seq[(ISpecVar, HType)],
                      specUniversal: Seq[IQuantifiedVar],
                      specExistential: Seq[IQuantifiedVar],
                      pre: IAssertion,
                      post: IAssertion
                     ) extends ISpecification {

    override def pp: String = {
      // TODO: make this use the general translation mechanism
      def getArgLitVal(v : ISpecVar, t: HType) : ISpecQuantifiedValue =
      (v, t) match {
          case (ISpecVar(name), HLocType()) => ISpecQuantifiedValue(s"l${name}")
          case (ISpecVar(name), _) => ISpecQuantifiedValue(s"v${name}")
        }

      val var_at = (v:ISpecVar, t: HType) => s"${t.pp}_at ${v.pp} ${getArgLitVal(v, t).pp}"
      val postExist =
        if (specExistential.nonEmpty)
          s"∃ ${specExistential.map(v => v.pp).mkString("  ")}, "
        else ""

      s"""
         |Lemma ${fname}_spec :
         |∀ ${specUniversal.map(v => v.pp).mkString(" ")},
         |${funArgs.map(v => var_at(v._1, v._2)).mkString(" →\n")} →
         |{{{ ${pre.pp} }}}
         |  ${fname} ${funArgs.map(v => v._1.pp).mkString(" ")}
         |{{{ RET #(); ${postExist}${post.pp} }}}.
         |""".stripMargin
    }
  }

}