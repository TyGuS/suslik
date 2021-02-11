package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.logic.Sentences.CAssertion
import org.tygus.suslik.certification.targets.htt.translation.IR.CGoal
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.targets.htt.translation.Translation.{translateExpr, translatePointsTo, translateSApp, translateSFormula}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic._

trait HTTTranslator[A,B] {
  def translate(value: A): B
}

object HTTTranslator {
  case class TranslatorException(msg: String) extends Exception(msg)

  implicit val binOpTranslator: HTTTranslator[BinOp, CBinOp] = {
    case OpImplication => COpImplication
    case OpPlus => COpPlus
    case OpMinus => COpMinus
    case OpMultiply => COpMultiply
    case OpEq => COpEq
    case OpBoolEq => COpBoolEq
    case OpLeq => COpLeq
    case OpLt => COpLt
    case OpAnd => COpAnd
    case OpOr => COpOr
    case OpUnion => COpUnion
    case OpDiff => COpDiff
    case OpIn => COpIn
    case OpSetEq => COpSetEq
    case OpSubset => COpSubset
    case OpIntersect => COpIntersect
  }
  implicit val unopTranslator: HTTTranslator[UnOp, CUnOp] = {
    case OpNot => COpNot
    case OpUnaryMinus => COpUnaryMinus
  }

  implicit val exprTranslator: HTTTranslator[Expr, CExpr] = (value: Expr) => {
    def visit(value: Expr): CExpr = value match {
      case Var(name) => CVar(name)
      case BoolConst(value) => CBoolConst(value)
      case LocConst(value) => CPtrConst(value)
      case IntConst(value) => CNatConst(value)
      case UnaryExpr(op, arg) => CUnaryExpr(op.translate, visit(arg))
      case BinaryExpr(op, left, right) => CBinaryExpr(op.translate, visit(left), visit(right))
      case SetLiteral(elems) => CSetLiteral(elems.map(visit))
      case IfThenElse(c, t, e) => CIfThenElse(visit(c), visit(t), visit(e))
      case _ => throw TranslatorException("Operation not supported")
    }
    visit(value)
  }

  implicit val varTranslator: HTTTranslator[Var, CVar] = (value: Var) => CVar(value.name)

  implicit val typeTranslator: HTTTranslator[SSLType, HTTType] = {
    case BoolType => CBoolType
    case IntType => CNatType
    case LocType => CPtrType
    case IntSetType => CNatSeqType
    case VoidType => CUnitType
    case CardType => CCardType
  }

  implicit val paramTranslator: HTTTranslator[(Var, SSLType), (CVar, HTTType)] =
    el => (el._1.translate, el._2.translate)

  implicit val sappTranslator: HTTTranslator[SApp, CSApp] = el => CSApp(el.pred, el.args.map(_.translate), el.card.translate)

  implicit val pointsToTranslator: HTTTranslator[PointsTo, CPointsTo] = el => CPointsTo(el.loc.translate, el.offset, el.value.translate)

  implicit val asnTranslator: HTTTranslator[Assertion, CAssertion] = el => {
    val conjuncts = el.phi.conjuncts.toSeq.map(c => translateExpr(c).simplify).filterNot(_.isCard)
    val f = (a1: CExpr, a2: CExpr) => CBinaryExpr(COpAnd, a1, a2)
    val phi = if (conjuncts.isEmpty) CBoolConst(true) else conjuncts.reduce(f)
    val sigma = translateSFormula(el.sigma)
    CAssertion(phi, sigma).removeCardConstraints
  }

  implicit val sFormulaTranslator: HTTTranslator[SFormula, CSFormula] = el => {
    val ptss = el.ptss.map(translatePointsTo)
    val apps = el.apps.map(translateSApp)
    CSFormula("h", apps, ptss)
  }

  implicit val goalTranslator: HTTTranslator[Goal, CGoal] = goal => {
    val pre = goal.pre.translate
    val post = goal.post.translate
    val gamma = goal.gamma.map(_.translate)
    val programVars = goal.programVars.map(_.translate)
    val universalGhosts = (pre.valueVars ++ post.valueVars).distinct.filter(v => goal.universalGhosts.contains(Var(v.name)))
    CGoal(pre, post, gamma, programVars, universalGhosts, goal.fname)
  }

  implicit val substTranslator: HTTTranslator[Map[Var, Expr], Map[CVar, CExpr]] = _.map {
    case (k, v) => k.translate -> v.translate
  }

  implicit val substVarTranslator: HTTTranslator[Map[Var, Var], Map[CVar, CVar]] = _.map {
    case (k, v) => k.translate -> v.translate
  }
}