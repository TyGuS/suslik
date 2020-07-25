package org.tygus.suslik.certification.targets.htt.language

import org.tygus.suslik.LanguageUtils.cardinalityPrefix
import org.tygus.suslik.logic.Specifications.selfCardVar

object Expressions {

  sealed abstract class CExpr extends ProgramPrettyPrinting {
    def isTrivial: Boolean = this == CBoolConst(true)
    def isCard: Boolean = this.vars.exists(_.isCard)

    def typeOf: Option[CoqType] = None

    def collect[R <: CExpr](p: CExpr => Boolean): Seq[R] = {

      def collector(acc: Seq[R])(exp: CExpr): Seq[R] = exp match {
        case v@CVar(_) if p(v) => acc :+ v.asInstanceOf[R]
        case c@CNatConst(_) if p(c) => acc :+ c.asInstanceOf[R]
        case c@CBoolConst(_) if p(c) => acc :+ c.asInstanceOf[R]
        case b@CBinaryExpr(_, l, r) =>
          val acc1 = if (p(b)) acc :+ b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          collector(acc2)(r)
        case u@CUnaryExpr(_, arg) =>
          val acc1 = if (p(u)) acc :+ u.asInstanceOf[R] else acc
          collector(acc1)(arg)
        case s@CSetLiteral(elems) =>
          val acc1 = if (p(s)) acc :+ s.asInstanceOf[R] else acc
          elems.foldLeft(acc1)((a,e) => collector(a)(e))
        case i@CIfThenElse(cond, l, r) =>
          val acc1 = if (p(i)) acc :+ i.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(cond)
          val acc3 = collector(acc2)(l)
          collector(acc3)(r)
        case a@CSApp(_, args, _) =>
          val acc1 = if (p(a)) acc :+ a.asInstanceOf[R] else acc
          args.foldLeft(acc1)((acc, arg) => collector(acc)(arg))
        case CPointsTo(loc, _, value) =>
          collector(collector(acc)(loc))(value)
        case CSFormula(_, apps, ptss) =>
          val acc1 = apps.foldLeft(acc)((a,e) => collector(a)(e))
          ptss.foldLeft(acc1)((a,e) => collector(a)(e))
        case _ => acc
      }

      collector(Seq.empty)(this)
    }

    def subst(sigma: Map[CVar, CExpr]): CExpr = this match {
      case v: CVar =>
        sigma.get(v).map(_.subst(sigma)).getOrElse(v)
      case CBinaryExpr(op, l, r) =>
        CBinaryExpr(op, l.subst(sigma), r.subst(sigma))
      case CUnaryExpr(op, arg) =>
        CUnaryExpr(op, arg.subst(sigma))
      case CSetLiteral(elems) =>
        CSetLiteral(elems.map(_.subst(sigma)))
      case CIfThenElse(cond, l, r) =>
        CIfThenElse(cond.subst(sigma), l.subst(sigma), r.subst(sigma))
      case CSApp(pred, args, card) =>
        CSApp(pred, args.map(_.subst(sigma)), card.subst(sigma))
      case CPointsTo(loc, offset, value) =>
        CPointsTo(loc.subst(sigma), offset, value.subst(sigma))
      case CSFormula(heapName, apps, ptss) =>
        val apps1 = apps.map(_.subst(sigma).asInstanceOf[CSApp])
        val ptss1 = ptss.map(_.subst(sigma).asInstanceOf[CPointsTo])
        CSFormula(heapName, apps1, ptss1)
      case _ =>
        this
    }

    def simplify: CExpr = this match {
      case CBinaryExpr(op, left, right) =>
        if (op == COpAnd) {
          if (left == CBoolConst(true) || left.isCard) return right.simplify
          else if (right == CBoolConst(true) || right.isCard) return left.simplify
        }
        CBinaryExpr(op, left.simplify, right.simplify)
      case CUnaryExpr(op, arg) =>
        CUnaryExpr(op, arg.simplify)
      case CSetLiteral(elems) =>
        CSetLiteral(elems.map(e => e.simplify))
      case CIfThenElse(cond, left, right) =>
        CIfThenElse(cond.simplify, left.simplify, right.simplify)
      case CSApp(pred, args, card) =>
        CSApp(pred, args.map(_.simplify), card)
      case other => other
    }

    def vars: Seq[CVar] = collect(_.isInstanceOf[CVar])
  }

  case class CVar(name: String) extends CExpr {
    override def pp: String = if (name.startsWith(cardinalityPrefix)) name.drop(cardinalityPrefix.length) else name
    override val isCard: Boolean = name.startsWith(cardinalityPrefix) || name == selfCardVar.name
  }

  case class CBoolConst(value: Boolean) extends CExpr {
    override def typeOf: Option[CoqType] = Some(CBoolType)
    override def pp: String = value.toString
  }

  case class CNatConst(value: Int) extends CExpr {
    override def typeOf: Option[CoqType] = Some(CNatType)
    override def pp: String = value.toString
  }

  case class CSetLiteral(elems: List[CExpr]) extends CExpr {
    override def typeOf: Option[CoqType] = Some(CNatSeqType)
    override def pp: String = if (elems.isEmpty) "nil" else s"[:: ${elems.map(_.pp).mkString("; ")}]"
    override def ppp: String = if (elems.isEmpty) "nil" else s"[:: ${elems.map(_.ppp).mkString("; ")}]"
  }

  case class CIfThenElse(cond: CExpr, left: CExpr, right: CExpr) extends CExpr {
    override def typeOf: Option[CoqType] = left.typeOf
    override def pp: String = s"if ${cond.pp} then ${left.pp} else ${right.pp}"
    override def ppp: String = s"if ${cond.ppp} then ${left.ppp} else ${right.ppp}"
  }

  case class CBinaryExpr(op: CBinOp, left: CExpr, right: CExpr) extends CExpr {
    override def typeOf: Option[CoqType] = op match {
      case COpPlus | COpMinus | COpMinus => Some(CNatType)
      case COpBoolEq | COpLeq | COpLt => Some(CBoolType)
      case COpAnd | COpOr | COpSetEq => Some(CPropType)
      case COpHeapJoin => Some(CHeapType)
      case COpUnion | COpDiff => Some(CNatSeqType)
      case _ => None
    }
    override def equals(that: Any): Boolean = that match {
      case CUnaryExpr(COpNot, COverloadedBinaryExpr(COpOverloadedEq, left1, right1)) => left == left1 && right == right1
      case CBinaryExpr(op1, left1, right1) => op == op1 && left == left1 && right == right1
      case COverloadedBinaryExpr(op1, left1, right1) => op == op1 && left == left1 && right == right1
      case _ => false
    }
    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"
    override def ppp: String = s"${left.ppp} ${op.ppp} ${right.ppp}"
  }

  case class CUnaryExpr(op: CUnOp, e: CExpr) extends CExpr {
    override def equals(that: Any): Boolean = that match {
      case CUnaryExpr(op1, e1) => op == op1 && e == e1
      case COverloadedBinaryExpr(COpNotEqual, left, right) => e match {
        case COverloadedBinaryExpr(COpOverloadedEq, left1, right1) => left == left1 && right == right1
        case _ => false
      }
      case _ => false
    }
    override def pp: String = s"${op.pp} ${e.pp}"
    override def ppp: String = s"${op.ppp} ${e.ppp}"
  }

  case class COverloadedBinaryExpr(op: COverloadedBinOp, left: CExpr, right: CExpr) extends CExpr {
    override def equals(that: Any): Boolean = that match {
      case CBinaryExpr(op1, left1, right1) => op == op1 && left == left1 && right == right1
      case COverloadedBinaryExpr(op1, left1, right1) => op == op1 && left == left1 && right == right1
      case _ => false
    }
    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"
    override def ppp: String = s"${left.ppp} ${op.ppp} ${right.ppp}"
  }

  case class CPointsTo(loc: CExpr, offset: Int = 0, value: CExpr) extends CExpr {
    def locPP: String = if (offset == 0) loc.pp else s"${loc.pp} .+ $offset"
    def locPPP: String = if (offset == 0) loc.ppp else s"${loc.ppp} .+ $offset"
    override def pp: String = if (value == CNatConst(0)) s"$locPP :-> null" else s"$locPP :-> ${value.pp}"
    override def ppp: String = if (value == CNatConst(0)) s"$locPPP :-> null" else s"$locPPP :-> ${value.ppp}"
  }

  case object CEmpty extends CExpr {
    override def pp: String = "empty"
  }

  case class CSApp(pred: String, var args: Seq[CExpr], card: CExpr) extends CExpr {
    override def pp: String = s"$pred ${args.map(arg => arg.pp).mkString(" ")}"
    override def ppp: String = s"$pred ${args.map(arg => arg.ppp).mkString(" ")}"

    val uniqueName: String = s"$pred${card.pp}"
    val heapName: String = s"h_$uniqueName"
    val hypName: String = s"H_$uniqueName"
  }

  case class CSFormula(heapName: String, apps: Seq[CSApp], ptss: Seq[CPointsTo]) extends CExpr {
    def unify(source: CSFormula): Map[CVar, CExpr] = {
      val initialMap: Map[CVar, CExpr] = Map.empty
      val m1 = source.ptss.zip(ptss).foldLeft(initialMap) {
        case (acc, (p1, p2)) => acc ++ p1.vars.zip(p2.vars).toMap
      }
      source.apps.zip(apps).foldLeft(m1) {
        case (acc, (a1, a2)) => acc ++ a1.vars.zip(a2.vars).toMap
      }
    }

    def ppHeap: String = if (ptss.isEmpty && apps.isEmpty) "empty" else {
      val ptssStr = ptss.map(_.pp)
      val appsStr = apps.map(_.heapName)
      (ptssStr ++ appsStr).mkString(" \\+ ")
    }

    override def pp: String = if (apps.isEmpty) s"$heapName = $ppHeap" else {
      val heapVarsStr = heapVars.map(_.pp)
      val appsStr = apps.zip(heapVarsStr).map { case (a, h) => s"${a.pp} $h"}.mkString(" /\\ ")
      s"$heapName = $ppHeap /\\ $appsStr"
    }

    val heapVars: Seq[CVar] = apps.map(a => CVar(a.heapName))
  }

  case class CExists(override val vars: Seq[CVar], e: CExpr) extends CExpr {
    override def pp: String = s"exists ${vars.map(v => v.pp).mkString(" ")}, ${e.pp}"
    override def ppp: String = s"exists ${vars.map(v => v.ppp).mkString(" ")}, ${e.ppp}"
  }

  case class CForAll(override val vars: Seq[CVar], e: CExpr) extends CExpr {
    override def pp: String = s"forall ${vars.map(v => v.pp).mkString(" ")}, ${e.pp}"
    override def ppp: String = s"forall ${vars.map(v => v.ppp).mkString(" ")}, ${e.ppp}"
  }

  case object Mystery extends CExpr {
    override def pp: String = "_"
    override def ppp: String = pp
  }

  sealed abstract class CUnOp extends ProgramPrettyPrinting

  object COpNot extends CUnOp {
    override def pp: String = "not"
  }

  object COpUnaryMinus extends CUnOp

  sealed abstract class COverloadedBinOp extends ProgramPrettyPrinting

  sealed abstract class CBinOp extends COverloadedBinOp

  object COpOverloadedEq extends COverloadedBinOp {
    override def equals(that: Any): Boolean = that match {
      case that: COpEq.type => true
      case that: COpOverloadedEq.type => true
      case _ => false
    }
    override def pp: String = "="
  }

  object COpNotEqual extends COverloadedBinOp {
    override def pp: String = "!="
  }

  object COpGt extends COverloadedBinOp {
    override def pp: String = ">"
  }

  object COpGeq extends COverloadedBinOp {
    override def pp: String = ">="
  }

  object COpOverloadedPlus extends COverloadedBinOp {
    override def pp: String = "+"
  }

  object COpOverloadedMinus extends COverloadedBinOp {
    override def pp: String = "-"
  }

  object COpOverloadedLeq extends COverloadedBinOp {
    override def pp: String = "<="
  }

  object COpOverloadedStar extends COverloadedBinOp {
    override def pp: String = "*"
  }

  object COpImplication extends CBinOp {
    override def pp: String = "->"
  }

  object COpPlus extends CBinOp {
    override def pp: String = "+"
  }

  object COpMinus extends CBinOp {
    override def pp: String = "-"
  }

  object COpMultiply extends CBinOp {
    override def pp: String = "*"
  }

  object COpEq extends CBinOp {
    override def equals(that: Any): Boolean = that match {
      case that: COpEq.type => true
      case that: COpOverloadedEq.type => true
      case _ => false
    }
    override def pp: String = "=="
    override def ppp: String = "=="
  }

  object COpBoolEq extends CBinOp {
    override def pp: String = "="
  }

  object COpLeq extends CBinOp {
    override def pp: String = "<="
  }

  object COpLt extends CBinOp {
    override def pp: String = "<"
  }

  object COpAnd extends CBinOp {
    override def pp: String = "/\\"
  }

  object COpOr extends CBinOp {
    override def pp: String = "\\/"
  }

  object COpHeapJoin extends CBinOp {
    override def pp: String = "\\+"
  }

  object COpUnion extends CBinOp {
    override def pp: String = "++"
  }

  object COpDiff extends CBinOp {
    override def pp: String = "--"
  }

  object COpIn extends CBinOp

  object COpSetEq extends CBinOp {
    override def pp: String = "="
  }

  object COpSubset extends CBinOp

  object COpIntersect extends CBinOp

}