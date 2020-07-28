package org.tygus.suslik.certification.targets.htt.language

import org.tygus.suslik.certification.targets.htt.language.Expressions._
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
        val ve = el.valueVars.diff(vars).distinct
        val he = el.heapVars
        val types = el.inferredTypes
        // existentials
        if (ve.nonEmpty) {
          builder.append(mkSpaces(offset))
          builder.append(s"exists ${ve.map(v => types.get(v).map(t => s"(${v.pp} : ${t.pp})").getOrElse(v.pp)).mkString(" ")},\n")
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
      case CInductiveClause(pred, idx, selector, asn) =>
        builder.append(mkSpaces(offset))
        builder.append(s"| $pred$idx of ${selector.pp} of\n")
        build(asn, offset + 2, vars)
      case CInductivePredicate(name, params, clauses) =>
        builder.append(mkSpaces(offset))
        builder.append(s"Inductive $name ${params.map{ case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")} : Prop :=\n")
        for (c <- clauses) {
          build(c, offset, vars)
          builder.append("\n")
        }
        builder.append(".")
      case el@CFunSpec(name, rType, params, pureParams, pre, post) =>
        val vprogs = "vprogs"
        val vghosts = "vghosts"

        def formalsToStr(formals: CFormals): (String, String) = {
          val (typs, names) = formals.unzip
          val typsStr = typs.map(_.pp).mkString(" * ")
          val namesStr = names.map(_.pp).mkString(", ")
          (typsStr, namesStr)
        }

        val (typsStr, namesStr) = formalsToStr(params)
        val (pureTypsStr, pureNamesStr) = formalsToStr(pureParams)

        // first line
        builder.append(mkSpaces(offset))
        builder.append(s"Definition ${name}_type ")
        builder.append(":=\n")

        // program var signatures
        if (params.nonEmpty) {
          builder.append(mkSpaces(offset + 2))
          builder.append(s"forall ($vprogs : $typsStr),\n")
        }

        // pure var signatures
        if (pureParams.nonEmpty) {
          builder.append(mkSpaces(offset + 2))
          builder.append(s"{($vghosts : $pureTypsStr)},\n")
        }

        // define goal
        builder.append(mkSpaces(offset + 4))
        builder.append("STsep (\n")

        // pre-condition
        builder.append(mkSpaces(offset + 6))
        builder.append("fun h =>\n")
        if (params.nonEmpty) {
          builder.append(mkSpaces(offset + 8))
          builder.append(s"let: ($namesStr) := $vprogs in\n")
        }
        if (pureParams.nonEmpty) {
          builder.append(mkSpaces(offset + 8))
          builder.append(s"let: ($pureNamesStr) := $vghosts in\n")
        }
        build(pre, offset + 8, el.programVars)
        builder.append(",\n")

        // post-condition
        builder.append(mkSpaces(offset + 6))
        builder.append(s"[vfun (_: ${rType.pp}) h =>\n")
        if (params.nonEmpty) {
          builder.append(mkSpaces(offset + 8))
          builder.append(s"let: ($namesStr) := $vprogs in\n")
        }
        if (pureParams.nonEmpty) {
          builder.append(mkSpaces(offset + 8))
          builder.append(s"let: ($pureNamesStr) := $vghosts in\n")
        }
        build(post, offset + 8, el.programVars)
        builder.append("\n")

        builder.append(mkSpaces(offset + 6))
        builder.append("]).")
    }

    build(this, 0, vars)
    builder.toString()
  }
}

case class CAssertion(phi: CExpr, sigma: CSFormula) extends Sentence {
  def unify(source: CAssertion): Map[CVar, CExpr] = {
    sigma.unify(source.sigma)
  }

  def subst(sub: Map[CVar, CExpr]): CAssertion =
    CAssertion(phi.subst(sub), sigma.subst(sub).asInstanceOf[CSFormula])

  val pureVars: Seq[CVar] =
    phi.vars.filterNot(_.isCard).distinct

  val spatialVars: Seq[CVar] =
    sigma.vars.filterNot(_.isCard).distinct

  val valueVars: Seq[CVar] =
    (spatialVars ++ pureVars).distinct

  val heapVars: Seq[CVar] =
    sigma.heapVars

  val inferredTypes: Map[CVar, CoqType] = {
    def collectPhi(el: CExpr, m: Map[CVar, CoqType]): Map[CVar, CoqType] = el match {
      case CBinaryExpr(COpSetEq, left: CVar, right: CVar) => m ++ Map(left -> CNatSeqType, right -> CNatSeqType)
      case CBinaryExpr(COpSetEq, left: CVar, right) => collectPhi(right, m ++ Map(left -> CNatSeqType))
      case CBinaryExpr(COpSetEq, left, right: CVar) => collectPhi(left, m ++ Map(right -> CNatSeqType))
      case _ => m
    }
    def collectSigma: Map[CVar, CoqType] = {
      val ptss = sigma.ptss
      ptss.foldLeft[Map[CVar, CoqType]](Map.empty){ case (acc, CPointsTo(loc, _, _)) => acc ++ Map(loc.asInstanceOf[CVar] -> CPtrType)}
    }
    val mPhi = collectPhi(phi, Map.empty)
    val mSigma = collectSigma
    mPhi ++ mSigma
  }
}

case class CInductiveClause(pred: String, idx: Int, selector: CExpr, asn: CAssertion) extends Sentence

case class CInductivePredicate(name: String, params: CFormals, clauses: Seq[CInductiveClause]) extends Sentence

case class CFunSpec(name: String, rType: CoqType, params: CFormals, pureParams: CFormals, pre: CAssertion, post: CAssertion) extends Sentence {
  def programVars: Seq[CVar] = params.map(_._2) ++ pureParams.map(_._2)
}