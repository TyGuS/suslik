package org.tygus.suslik.certification.targets.coq.language

import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.util.StringUtil.mkSpaces

sealed abstract class Sentence extends PrettyPrinting {
  def vars: Seq[CVar] = this match {
    case CInductivePredicate(_, params, _) => params.map(_._2)
    case _ => Seq.empty
  }

  override def pp: String = {
    val builder = new StringBuilder()

    def build(el: Sentence, offset: Int = 0, vars: Seq[CVar] = Seq.empty) : Unit = el match {
      case el@CAssertion(phi, sigma) =>
        val ve = (el.spatialEx ++ el.pureEx).diff(vars).distinct
        val he = el.heapEx
        // existentials
        if (ve.nonEmpty) {
          builder.append(mkSpaces(offset))
          builder.append(s"exists ${ve.map(_.pp).mkString(" ")},\n")
        }
        if (he.nonEmpty) {
          builder.append(mkSpaces(offset))
          builder.append(s"exists ${he.map(_.pp).mkString(" ")},\n")
        }
        // body
        builder.append(mkSpaces(offset + 2))
        phi match {
          case CBoolConst(true) => builder.append(sigma.pp)
          case _ => builder.append(s"${phi.pp} /\\ ${sigma.pp}")
        }
      case CInductiveClause(name, selector, asn) =>
        builder.append(mkSpaces(offset))
        builder.append(s"| $name of ${selector.pp} of\n")
        build(asn, offset + 2, vars)
      case CInductivePredicate(name, params, clauses) =>
        builder.append(mkSpaces(offset))
        builder.append(s"Inductive $name ${params.map{ case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")} : Prop :=\n")
        for (c <- clauses) {
          build(c, offset, vars)
          builder.append("\n")
        }
        builder.append(".")
      case el@CFunSpec(name, rType, params, pureParams, pre, post, inductive) =>
        val paramsStr = params.map { case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")
        builder.append(mkSpaces(offset))
        builder.append(s"Definition ${name}_type ")
        builder.append(":=\n")
        builder.append(s"  forall $paramsStr,\n")

        // print pure params
        if (pureParams.nonEmpty) {
          builder.append(mkSpaces(offset + 2))
          builder.append(s"{${pureParams.map { case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")}},\n")
        }

        // define goal
        builder.append(mkSpaces(offset + 4))
        builder.append("STsep (\n")

        // pre-condition
        builder.append(mkSpaces(offset + 6))
        builder.append("fun h =>\n")
        build(pre, offset + 8, el.programVars)
        builder.append(",\n")

        // post-condition
        builder.append(mkSpaces(offset + 6))
        builder.append(s"[vfun (_: ${rType.pp}) h =>\n")
        build(post, offset + 8, el.programVars)

        builder.append(mkSpaces(offset + 6))
        builder.append("]).")
    }

    build(this, 0, vars)
    builder.toString()
  }
}

case class CAssertion(phi: CExpr, sigma: CSFormula) extends Sentence {
  def pureEx: Seq[CVar] =
    phi.collect(_.isInstanceOf[CVar]).toSeq

  def spatialEx: Seq[CVar] =
    sigma.collect(_.isInstanceOf[CVar]).toSeq

  def heapEx: Seq[CVar] =
    sigma.heapVars
}

case class CInductiveClause(name: String, selector: CExpr, asn: CAssertion) extends Sentence

case class CInductivePredicate(name: String, params: CFormals, clauses: Seq[CInductiveClause]) extends Sentence

case class CFunSpec(name: String, rType: CoqType, params: CFormals, pureParams: CFormals, pre: CAssertion, post: CAssertion, inductive: Boolean) extends Sentence {
  def programVars: Seq[CVar] = params.map(_._2) ++ pureParams.map(_._2)
}