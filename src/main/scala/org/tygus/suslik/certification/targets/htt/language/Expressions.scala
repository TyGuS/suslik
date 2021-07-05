package org.tygus.suslik.certification.targets.htt.language

import org.tygus.suslik.LanguageUtils.cardinalityPrefix
import org.tygus.suslik.logic.Specifications.selfCardVar

object Expressions {
  type CSubst = Map[CVar, CExpr]
  type CSubstVar = Map[CVar, CVar]

  sealed abstract class CExpr extends PrettyPrinting {
    def isCard: Boolean = this.vars.exists(_.isCard)

    def collect[R <: CExpr](p: CExpr => Boolean): Seq[R] = {

      def collector(acc: Seq[R])(exp: CExpr): Seq[R] = exp match {
        case v@CVar(_) if p(v) => acc :+ v.asInstanceOf[R]
        case c@CNatConst(_) if p(c) => acc :+ c.asInstanceOf[R]
        case c@CPtrConst(_) if p(c) => acc :+ c.asInstanceOf[R]
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
        case a@CSApp(_, args, card) =>
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

    def subst(sigma: CSubst): CExpr = this match {
      case v: CVar =>
        sigma.get(v) match {
          case None => v
          case Some(e) if v == e => v
          case Some(e) => e.subst(sigma)
        }
      case CBinaryExpr(op, l, r) =>
        CBinaryExpr(op, l.subst(sigma), r.subst(sigma))
      case CUnaryExpr(op, arg) =>
        CUnaryExpr(op, arg.subst(sigma))
      case CSetLiteral(elems) =>
        CSetLiteral(elems.map(_.subst(sigma)))
      case CIfThenElse(cond, l, r) =>
        CIfThenElse(cond.subst(sigma), l.subst(sigma), r.subst(sigma))
      case _ =>
        this
    }

    def substExpr(sigma: Map[CExpr, CExpr]): CExpr = sigma.get(this) match {
      case Some(e) => e
      case None => this match {
        case v: CVar => v
        case CBinaryExpr(op, left, right) => CBinaryExpr(op, left.substExpr(sigma), right.substExpr(sigma))
        case CUnaryExpr(op, arg) => CUnaryExpr(op, arg.substExpr(sigma))
        case CSetLiteral(elems) => CSetLiteral(elems.map(_.substExpr(sigma)))
        case CIfThenElse(cond, left, right) => CIfThenElse(cond, left.substExpr(sigma), right.substExpr(sigma))
        case CSApp(pred, args, card) => CSApp(pred, args.map(_.substExpr(sigma)), card.substExpr(sigma))
        case CPointsTo(loc, offset, value) => CPointsTo(loc.substExpr(sigma), offset, value.substExpr(sigma))
        case _ => this
      }
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

    def cardVars: Seq[CVar] = collect(_.isInstanceOf[CSApp]).flatMap {v: CSApp => v.card.vars}

    def ppProp: String = pp
  }

  case class CVar(name: String) extends CExpr {
    override def pp: String = if (name.startsWith(cardinalityPrefix)) name.drop(cardinalityPrefix.length) else name
    override val isCard: Boolean = name.startsWith(cardinalityPrefix) || name == selfCardVar.name
    def substVar(sub: CSubst): CVar = sub.get(this) match {
      case Some(v@CVar(_)) => v
      case _ => this
    }
  }

  case class CBoolConst(value: Boolean) extends CExpr {
    override def pp: String = value.toString
  }

  case class CNatConst(value: Int) extends CExpr {
    override def pp: String = value.toString
  }

  case class CPtrConst(value: Int) extends CExpr {
    override def pp: String = if (value == 0) "null" else value.toString
  }

  case class CSetLiteral(elems: List[CExpr]) extends CExpr {
    override def pp: String = if (elems.isEmpty) "@nil nat" else s"[:: ${elems.map(_.pp).mkString("; ")}]"
  }

  case class CIfThenElse(cond: CExpr, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String = s"(if ${cond.pp} then ${left.pp} else ${right.pp})"
  }

  case class CBinaryExpr(op: CBinOp, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String = op match {
      case COpSubset => s"@sub_mem nat_eqType (mem (${left.pp})) (mem (${right.pp}))"
      case COpSetEq => s"@perm_eq nat_eqType (${left.pp}) (${right.pp})"
      case _ => s"(${left.pp}) ${op.pp} (${right.pp})"
    }

    override def ppProp: String = op match {
      case COpEq => s"(${left.pp}) ${op.ppProp} (${right.pp})"
      case _ => pp
    }
  }

  case class CUnaryExpr(op: CUnOp, e: CExpr) extends CExpr {
    override def pp: String = s"${op.pp} (${e.pp})"
  }

  case class CPointsTo(loc: CExpr, offset: Int = 0, value: CExpr) extends CExpr {
    def locPP: String = if (offset == 0) loc.pp else s"${loc.pp} .+ $offset"
    override def pp: String = s"$locPP :-> (${value.pp})"
    override def subst(sigma: CSubst): CPointsTo =
      CPointsTo(loc.subst(sigma), offset, value.subst(sigma))
  }

  case class CSApp(pred: String, var args: Seq[CExpr], card: CExpr) extends CExpr {
    override def pp: String = s"$pred ${args.map(arg => arg.pp).mkString(" ")}"

    override def subst(sigma: CSubst): CSApp =
      CSApp(pred, args.map(_.subst(sigma)), card.subst(sigma))

    val uniqueName: String = s"${pred}_${args.flatMap(_.vars).map(_.pp).mkString("")}_${card.vars.map(_.pp).mkString("")}"
    val heapName: String = s"h_$uniqueName"
    val hypName: String = s"H_$uniqueName"
  }

  case class CSFormula(heapName: String, apps: Seq[CSApp], ptss: Seq[CPointsTo]) extends CExpr {
    def unify(source: CSFormula): CSubstVar = {
      val initialMap: CSubstVar = Map.empty
      val m1 = source.ptss.zip(ptss).foldLeft(initialMap) {
        case (acc, (p1, p2)) => acc ++ p1.vars.zip(p2.vars).filterNot(v => v._1 == v._2).toMap
      }
      source.apps.zip(apps).foldLeft(m1) {
        case (acc, (a1, a2)) => acc ++ a1.vars.zip(a2.vars).filterNot(v => v._1 == v._2).toMap
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

    override def subst(sigma: CSubst): CSFormula = {
      val apps1 = apps.map(_.subst(sigma))
      val ptss1 = ptss.map(_.subst(sigma))
      CSFormula(heapName, apps1, ptss1)
    }

    val heapVars: Seq[CVar] = apps.map(a => CVar(a.heapName))
  }

  sealed abstract class CUnOp extends PrettyPrinting

  object COpNot extends CUnOp {
    override def pp: String = "~~"
  }

  object COpUnaryMinus extends CUnOp

  sealed abstract class CBinOp extends PrettyPrinting {
    def ppProp: String = pp
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
    override def ppProp: String = "="
    override def pp: String = "=="
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
    override def pp: String = "&&"
  }

  object COpOr extends CBinOp {
    override def pp: String = "||"
  }

  object COpUnion extends CBinOp {
    override def pp: String = "++"
  }

  object COpDiff extends CBinOp {
    override def pp: String = "--"
  }

  object COpIn extends CBinOp

  object COpSetEq extends CBinOp

  object COpSubset extends CBinOp {
    override def pp: String = "<="
  }

  object COpIntersect extends CBinOp

}