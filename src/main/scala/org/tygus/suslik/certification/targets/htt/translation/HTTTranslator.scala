package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.logic.Proof
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CAssertion, CPFormula}
import org.tygus.suslik.certification.targets.htt.program.Statements._
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic._

trait HTTTranslator[A,B] {
  def translate(value: A)(implicit env: Environment): B
}

object HTTTranslator {
  case class TranslatorException(msg: String) extends Exception(msg)

  implicit val binOpTranslator: HTTTranslator[BinOp, CBinOp] = new HTTTranslator[BinOp, CBinOp] {
    override def translate(value: BinOp)(implicit env: Environment): CBinOp = value match {
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
      case OpSetEq => if (env.config.certSetRepr) COpSetEq else COpEq
      case OpSubset => COpSubset
      case OpIntersect => COpIntersect
    }
  }

  implicit val unopTranslator: HTTTranslator[UnOp, CUnOp] = new HTTTranslator[UnOp, CUnOp] {
    override def translate(value: UnOp)(implicit env: Environment): CUnOp = value match {
      case OpNot => COpNot
      case OpUnaryMinus => COpUnaryMinus
    }
  }

  implicit val exprTranslator: HTTTranslator[Expr, CExpr] = new HTTTranslator[Expr, CExpr] {
    override def translate(value: Expr)(implicit env: Environment): CExpr = {
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
  }

  implicit val varTranslator: HTTTranslator[Var, CVar] = new HTTTranslator[Var, CVar] {
    override def translate(value: Var)(implicit env: Environment): CVar = CVar(value.name)
  }

  implicit val mallocTranslator: HTTTranslator[Statements.Malloc, CMalloc] = new HTTTranslator[Statements.Malloc, CMalloc] {
    override def translate(stmt: Statements.Malloc)(implicit env: Environment): CMalloc =
      CMalloc(stmt.to.translate, stmt.tpe.translate, stmt.sz)
  }
  implicit val loadTranslator: HTTTranslator[Statements.Load, CLoad] = new HTTTranslator[Statements.Load, CLoad] {
    override def translate(stmt: Statements.Load)(implicit env: Environment): CLoad =
      CLoad(stmt.to.translate, stmt.tpe.translate, stmt.from.translate, stmt.offset)
  }
  implicit val storeTranslator: HTTTranslator[Statements.Store, CStore] = new HTTTranslator[Statements.Store, CStore] {
    override def translate(stmt: Statements.Store)(implicit env: Environment): CStore =
      CStore(stmt.to.translate, stmt.offset, stmt.e.translate)
  }
  implicit val callTranslator: HTTTranslator[Statements.Call, CCall] = new HTTTranslator[Statements.Call, CCall] {
    override def translate(stmt: Statements.Call)(implicit env: Environment): CCall =
      CCall(stmt.fun.translate, stmt.args.map(_.translate))
  }

  implicit val typeTranslator: HTTTranslator[SSLType, HTTType] = new HTTTranslator[SSLType, HTTType] {
    override def translate(value: SSLType)(implicit env: Environment): HTTType = value match {
      case BoolType => CBoolType
      case IntType => CNatType
      case LocType => CPtrType
      case IntSetType => CNatSeqType
      case VoidType => CUnitType
      case CardType => CCardType
    }
  }

  implicit val paramTranslator: HTTTranslator[(Var, SSLType), (CVar, HTTType)] = new HTTTranslator[(Var, SSLType), (CVar, HTTType)] {
    override def translate(el: (Var, SSLType))(implicit env: Environment): (CVar, HTTType) = (el._1.translate, el._2.translate)
  }

  implicit val sappTranslator: HTTTranslator[SApp, CSApp] = new HTTTranslator[SApp, CSApp] {
    override def translate(el: SApp)(implicit env: Environment): CSApp = CSApp(el.pred, el.args.map(_.translate), el.card.translate)
  }

  implicit val pointsToTranslator: HTTTranslator[PointsTo, CPointsTo] = new HTTTranslator[PointsTo, CPointsTo] {
    override def translate(el: PointsTo)(implicit env: Environment): CPointsTo = CPointsTo(el.loc.translate, el.offset, el.value.translate)
  }

  implicit val asnTranslator: HTTTranslator[Assertion, CAssertion] = new HTTTranslator[Assertion, CAssertion] {
    override def translate(el: Assertion)(implicit env: Environment): CAssertion = CAssertion(el.phi.translate, el.sigma.translate).removeCardConstraints
  }

  implicit val pFormulaTranslator: HTTTranslator[PFormula, CPFormula] = new HTTTranslator[PFormula, CPFormula] {
    override def translate(el: PFormula)(implicit env: Environment): CPFormula = CPFormula(el.conjuncts.toSeq.map(c => c.translate.simplify).filterNot(_.isCard))
  }

  implicit val sFormulaTranslator: HTTTranslator[SFormula, CSFormula] = new HTTTranslator[SFormula, CSFormula] {
    override def translate(el: SFormula)(implicit env: Environment): CSFormula = {
      val ptss = el.ptss.map(_.translate)
      val apps = el.apps.map(_.translate)
      CSFormula("h", apps, ptss)
    }
  }

  implicit val goalTranslator: HTTTranslator[Goal, Proof.Goal] = new HTTTranslator[Goal, Proof.Goal] {
    override def translate(goal: Goal)(implicit env: Environment): Proof.Goal = {
      val pre = goal.pre.translate
      val post = goal.post.translate
      val gamma = goal.gamma.map(_.translate)
      val programVars = goal.programVars.map(_.translate)
      val universalGhosts = (pre.valueVars ++ post.valueVars).distinct.filter(v => goal.universalGhosts.contains(Var(v.name)))
      Proof.Goal(pre, post, gamma, programVars, universalGhosts, goal.fname)
    }
  }

  implicit val substTranslator: HTTTranslator[Map[Var, Expr], Map[CVar, CExpr]] = new HTTTranslator[Map[Var, Expr], Map[CVar, CExpr]] {
    override def translate(el: Map[Var, Expr])(implicit env: Environment): Map[CVar, CExpr] = el.map {
      case (k, v) => k.translate -> v.translate
    }
  }

  implicit val substVarTranslator: HTTTranslator[Map[Var, Var], Map[CVar, CVar]] = new HTTTranslator[Map[Var, Var], Map[CVar, CVar]] {
    override def translate(el: Map[Var, Var])(implicit env: Environment): Map[CVar, CVar] = el.map {
      case (k, v) => k.translate -> v.translate
    }
  }

  implicit val substExprTranslator: HTTTranslator[Map[Expr, Expr], Map[CExpr, CExpr]] = new HTTTranslator[Map[Expr, Expr], Map[CExpr, CExpr]] {
    override def translate(el: Map[Expr, Expr])(implicit env: Environment): Map[CExpr, CExpr] = el.map {
      case (k, v) => k.translate -> v.translate
    }
  }

  implicit val gammaTranslator: HTTTranslator[Map[Var, SSLType], Map[CVar, HTTType]] = new HTTTranslator[Map[Var, SSLType], Map[CVar, HTTType]] {
    override def translate(el: Map[Var, SSLType])(implicit env: Environment): Map[CVar, HTTType] = el.map {
      case (k, v) => k.translate -> v.translate
    }
  }
}