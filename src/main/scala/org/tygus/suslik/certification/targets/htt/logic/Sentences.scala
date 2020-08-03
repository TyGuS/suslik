package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.{CFormals, PrettyPrinting}
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.logic.Proof.Subst

object Sentences {
  case class CAssertion(phi: CExpr, sigma: CSFormula) extends PrettyPrinting {
    override def pp: String = if (phi.isTrivial) sigma.pp else s"${phi.pp} /\\ ${sigma.pp}"

    def existentials(quantifiedVars: Seq[CVar]): Seq[CVar] = valueVars.diff(quantifiedVars)

    def ppQuantified(quantifiedVars: Seq[CVar], depth: Int = 0): String = {
      val builder = new StringBuilder()

      val valueEx = existentials(quantifiedVars)
      val heapEx = heapVars
      if (valueEx.nonEmpty) {
        builder.append(s"exists ${valueEx.map(v => inferredTypes.get(v).map(t => s"(${v.pp} : ${t.pp})").getOrElse(v.pp)).mkString(" ")},\n")
      }
      if (heapEx.nonEmpty) {
        builder.append(s"exists ${heapEx.map(_.pp).mkString(" ")},\n")
      }

      builder.append(pp)

      getIndent(depth) + builder.toString().replaceAll("\n", s"\n${getIndent(depth)}")
    }

    def subst(sub: Subst): CAssertion =
      CAssertion(phi.subst(sub), sigma.subst(sub))

    val valueVars: Seq[CVar] =
      (phi.vars ++ sigma.vars).distinct.filterNot(_.isCard)

    val heapVars: Seq[CVar] =
      sigma.heapVars

    val inferredTypes: Map[CVar, HTTType] = {
      @scala.annotation.tailrec
      def collectPhi(el: CExpr, m: Map[CVar, HTTType]): Map[CVar, HTTType] = el match {
        case CBinaryExpr(COpSetEq, left: CVar, right: CVar) => m ++ Map(left -> CNatSeqType, right -> CNatSeqType)
        case CBinaryExpr(COpSetEq, left: CVar, right) => collectPhi(right, m ++ Map(left -> CNatSeqType))
        case CBinaryExpr(COpSetEq, left, right: CVar) => collectPhi(left, m ++ Map(right -> CNatSeqType))
        case _ => m
      }
      def collectSigma: Map[CVar, HTTType] = {
        val ptss = sigma.ptss
        ptss.foldLeft[Map[CVar, HTTType]](Map.empty){ case (acc, CPointsTo(loc, _, _)) => acc ++ Map(loc.asInstanceOf[CVar] -> CPtrType)}
      }
      val mPhi = collectPhi(phi, Map.empty)
      val mSigma = collectSigma
      mPhi ++ mSigma
    }
  }

  case class CInductiveClause(pred: String, idx: Int, selector: CExpr, asn: CAssertion, existentials: Seq[CExpr]) extends PrettyPrinting {
    def subst(sub: Subst): CInductiveClause =
      CInductiveClause(pred, idx, selector.subst(sub), asn.subst(sub), existentials.map(_.subst(sub)))
  }

  case class CInductivePredicate(name: String, params: CFormals, clauses: Seq[CInductiveClause]) extends PrettyPrinting {
    val paramVars: Seq[CVar] = params.map(_._2)

    def subst(sub: Subst): CInductivePredicate =
      CInductivePredicate(name, params.map(p => (p._1, p._2.substVar(sub))), clauses.map(_.subst(sub)))

    override def pp: String = {
      val builder = new StringBuilder()
      builder.append(s"Inductive $name ${params.map{ case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")} : Prop :=\n")

      // clauses
      val clausesStr = for {
        CInductiveClause(pred, idx, selector, asn, _) <- clauses
      } yield s"| $pred$idx of ${selector.pp} of\n${asn.ppQuantified(paramVars, 1)}"

      builder.append(s"${clausesStr.mkString("\n")}.\n")
      builder.toString()
    }
  }

  case class CFunSpec(name: String, rType: HTTType, params: CFormals, ghostParams: CFormals, pre: CAssertion, post: CAssertion) extends PrettyPrinting {
    val paramVars: Seq[CVar] = params.map(_._2)
    val ghostParamVars: Seq[CVar] = ghostParams.map(_._2)

    val progVarsAlias = "vprogs"
    val ghostVarsAlias = "vghosts"

    private def ppFormals(formals: CFormals): (String, String) = {
      val (typs, names) = formals.unzip
      val typsStr = typs.map(_.pp).mkString(" * ")
      val namesStr = names.map(_.pp).mkString(", ")
      (typsStr, namesStr)
    }

    override def pp: String = {
      val builder = new StringBuilder()

      val (typsStr, progVarsStr) = ppFormals(params)
      val (ghostTypsStr, ghostVarsStr) = ppFormals(ghostParams)
      val destructuredAliases = {
        val destructuredParams = if (params.nonEmpty) s"${getIndent(3)}let: ($progVarsStr) := $progVarsAlias in\n" else ""
        val destructuredGhostParams = if (ghostParams.nonEmpty) s"${getIndent(3)}let: ($ghostVarsStr) := $ghostVarsAlias in\n" else ""
        destructuredParams + destructuredGhostParams
      }

      builder.append(s"Definition ${name}_type :=\n")

      // program var signatures
      if (params.nonEmpty) {
        builder.append(s"${getIndent(1)}forall ($progVarsAlias : $typsStr),\n")
      }

      // ghost var signatures
      if (ghostParams.nonEmpty) {
        builder.append(s"${getIndent(1)}{($ghostVarsAlias : $ghostTypsStr)},\n")
      }

      builder.append(s"${getIndent(1)}STsep (\n")

      // pre-condition
      builder.append(s"${getIndent(2)}fun h =>\n")
      builder.append(destructuredAliases)
      builder.append(pre.ppQuantified(paramVars ++ ghostParamVars, 3))
      builder.append(",\n")

      // post-condition
      builder.append(s"${getIndent(2)}[vfun (_: ${rType.pp}) h =>\n")
      builder.append(destructuredAliases)
      builder.append(post.ppQuantified(paramVars ++ ghostParamVars, 3))
      builder.append("\n")

      builder.append(s"${getIndent(2)}]).")

      builder.toString()
    }
  }
}
