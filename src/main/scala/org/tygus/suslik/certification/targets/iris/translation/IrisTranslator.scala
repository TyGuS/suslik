package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions._
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HCardType, HIntSetType, HIntType, HLocType, HType, HUnknownType, HValType}
import org.tygus.suslik.certification.targets.iris.logic.Assertions._
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.targets.iris.translation.Translation.TranslationException
import org.tygus.suslik.certification.translation.{CardConstructor, PredicateTranslation}
import org.tygus.suslik.language.Expressions.{OpEq, _}
import org.tygus.suslik.language.Statements.{Call, Load, Malloc, Store}
import org.tygus.suslik.language.{CardType, Expressions, Ident, IntSetType, IntType, LocType, SSLType}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic._

trait IrisTranslator[From, To] {
  def translate(value: From, ctx: Option[ProgramTranslationContext] = None, target: Option[HType] = None): To
}

object IrisTranslator {
  case class TranslatorException(msg: String) extends Exception(msg)

  implicit val binOpTranslator: IrisTranslator[BinOp, HBinOp] = (value, _, _) => value match {
    case OpPlus => HOpPlus
    case OpMinus => HOpMinus
    case OpMultiply => HOpMultiply
    case OpEq | OpBoolEq => HOpEq
    case OpLeq => HOpLe
    case OpLt => HOpLt
    case OpSetEq => HOpSetEq
    case OpUnion => HOpUnion
    case _ => ???
  }

  implicit val paramTranslator: IrisTranslator[(Var, SSLType), HProgVar] = (el, _, _) => el._1.translate

  implicit val unopTranslator: IrisTranslator[UnOp, HUnOp] = (value, _, _) => value match {
    case OpNot => HOpNot
    case OpUnaryMinus => HOpUnaryMinus
  }

  implicit val exprTranslator: IrisTranslator[Expr, HExpr] = (expr, ctx, _) => {
    def visit(expr: Expr): HExpr = expr match {
      case Var(name) => HProgVar(name)
      case IntConst(v) => HLitInt(v)
      case LocConst(v) => HLitLoc(v)
      case BoolConst(v) => HLitBool(v)
      case SetLiteral(elems) => HSetLiteral(elems.map(_.translate(exprTranslator, ctx)))
      case UnaryExpr(op, arg) => HUnaryExpr(op.translate, visit(arg))
      // Hack for null-pointer comparison
      case BinaryExpr(OpEq, v:Var, IntConst(value)) if ctx.get.gamma.get(v).contains(LocType) && value == 0 =>
        HBinaryExpr(HOpEq, visit(v), HLitLoc(0))
      case BinaryExpr(op, left, right) => HBinaryExpr(op.translate, visit(left), visit(right))
      case IfThenElse(cond, t, f) => HIfThenElse(visit(cond), visit(t), visit(f))
//      case OverloadedBinaryExpr(op, left, right) => HBinaryExpr(op.translate, visit(left), visit(right))
    }

    // FIXME: we should probably guarantee that the context gets passed also during program translation
    // (it does get passed during spec translation, I think)
    val e = if (ctx.isDefined) expr.resolveOverloading(ctx.get.hctx.translate) else expr
    visit(e)
  }

  implicit val progVarTranslator: IrisTranslator[Var, HProgVar] = (pv, _, _) => HProgVar(pv.name)
  implicit val progVarToSpecVar: IrisTranslator[HProgVar, ISpecVar] = (hv, ctx, _) =>
    ISpecVar(hv.name, ctx.get.hctx(hv.name))

  implicit val typeTranslator: IrisTranslator[SSLType, HType] = (value, _, _) => value match {
    case IntType => HIntType()
    case LocType => HLocType()
    case IntSetType => HIntSetType()
    case CardType => HUnknownType()
    case _ => ???
  }

  implicit val reverseTypeTranslator: IrisTranslator[HType, SSLType] = (value, _, _) => value match {
    case HIntType() => IntType
    case HLocType() => LocType
    case HIntSetType() => IntSetType
    case HCardType(_) | HUnknownType() => CardType
    case _ => ???
  }

  implicit val gammaTranslator: IrisTranslator[Gamma, Map[Ident, HType]] = (g, _ , _) => {
    g.map({ case (v, t) => (v.name, t.translate) })
  }

  implicit val reverseGammaTranslator: IrisTranslator[Map[Ident, HType], Gamma] = (h, _, _) => {
    h.map( {case (v, t) => (Var(v), t.translate)})
  }

  implicit val mallocTranslator: IrisTranslator[Malloc, HLet] =
    (stmt, _, _) => HLet(stmt.to.translate, HAllocN(HLitInt(stmt.sz), HLitUnit()), HLitUnit())
  implicit val loadTranslator: IrisTranslator[Load, HLet] =
    (stmt, _, _) => {
      val baseVar = stmt.from.translate
      val fromAddr = if (stmt.offset == 0) baseVar else HBinaryExpr(HOpOffset, baseVar, HLitLoc(stmt.offset))
      HLet(stmt.to.translate, HLoad(fromAddr), HLitUnit())
    }
  implicit val storeTranslator: IrisTranslator[Store, HStore] =
    (stmt, _, _) => {
      val baseVar = stmt.to.translate
      val toAddr = if (stmt.offset == 0) baseVar else HBinaryExpr(HOpOffset, baseVar, HLitLoc(stmt.offset))
      HStore(toAddr, stmt.e.translate)
    }

  implicit val callTranslator: IrisTranslator[Call, HCall] = (stmt, _, _) => HCall(stmt.fun.translate, stmt.args.map(_.translate))

  implicit val phiTranslator: IrisTranslator[PFormula, IPureAssertion] = (f, ctx, _) => {
    assert(ctx.isDefined)
    IAnd(f.conjuncts.map(_.translate(exprTranslator, ctx).translate(toSpecExpr, ctx)).toSeq)
  }

  /***
    * FIXME: This is going to be a major source of bugs.
    * This method performs a crappy version of type inference to figure out when something needs to be printed
    * as a HeapLang value and when it needs to be printed as a raw Coq term
    */
  implicit val toSpecExpr: IrisTranslator[HExpr, IPureAssertion] = (expr, ctx, target) => {
    assert(ctx.isDefined)
    val c = ctx.get

    def shouldPrintAsVal(expr: HExpr):Boolean = expr match {
      // heaplang does not support set values
      case HProgVar(n) => !c.hctx.get(n).contains(HIntSetType())
      case HUnaryExpr(_, e) => shouldPrintAsVal(e)
      case HBinaryExpr(HOpUnion, _, _) => false
      case HBinaryExpr(_, left, right) => shouldPrintAsVal(left) && shouldPrintAsVal(right)
      case _ => true
    }

    val prodVal = target.isDefined && target.get.isValType
    val subTarget = if (prodVal && shouldPrintAsVal(expr)) target else None

    expr match {
      case v: HProgVar =>
        val specVar = v.translate(progVarToSpecVar, ctx)
        if (prodVal) ISpecMakeVal(specVar) else specVar
      case l: HLit => ISpecLit(l)
      case HBinaryExpr(op, left, right) => ISpecBinaryExpr(op, left.translate(toSpecExpr, ctx, subTarget), right.translate(toSpecExpr, ctx, subTarget))
      case HUnaryExpr(op, expr) => ISpecUnaryExpr(op, expr.translate(toSpecExpr, ctx, subTarget))
      case HSetLiteral(elems) => ISetLiteral(elems.map(_.translate(toSpecExpr, ctx, subTarget)))
      case HIfThenElse(cond, left, right) => ISpecIfThenElse(cond.translate(toSpecExpr, ctx, subTarget), left.translate(toSpecExpr, ctx, subTarget), right.translate(toSpecExpr, ctx, subTarget))
      case _ => ???
    }
  }

  implicit val pointsToTranslator: IrisTranslator[PointsTo, IPointsTo] = (f, ctx, _) => {
    val base = f.loc.translate(exprTranslator, ctx).translate(toSpecExpr, ctx)
    val loc = if (f.offset > 0) ISpecBinaryExpr(HOpOffset, base, ISpecLit(HLitOffset(f.offset))) else base
    // Sometimes we get PointsTo(Var(x), 0, LocConst(0)) when we should get an IntConst
    val valToTranslate = f.value match {
      case LocConst(v) if v == 0 => IntConst(0)
      case _ => f.value
    }
    val value = valToTranslate.translate(exprTranslator, ctx).translate(toSpecExpr, ctx, Some(HValType()))
    IPointsTo(loc, value)
  }

  implicit val predAppTranslator: IrisTranslator[SApp, IPredApp] = (pa, ctx, _) => {
    assert(ctx.isDefined)
    IPredApp(pa.pred, pa.args.map(_.translate(exprTranslator, ctx).translate(toSpecExpr, ctx)), pa.card.translate(exprTranslator, ctx).translate(toSpecExpr, ctx))
  }

  implicit val heapleatTranslator: IrisTranslator[Heaplet, ISpatialAssertion] = (h, ctx, _) => {
    assert(ctx.isDefined)
    h match {
      case pt:PointsTo => pt.translate(pointsToTranslator, ctx)
      case _:Block => IBlock()
      case pa:SApp => pa.translate(predAppTranslator, ctx)
      case _ => ???
    }
  }

  implicit val sigmaTranslator: IrisTranslator[SFormula, ISpatialAssertion] = (f, ctx, _) => {
    IHeap(f.chunks.map(_.translate(heapleatTranslator, ctx)))
  }

  implicit val assertionTranslator: IrisTranslator[Assertion, IAssertion] = (f, ctx, _) => {
    assert(ctx.isDefined)
    IAssertion(f.phi.translate(phiTranslator, ctx), f.sigma.translate(sigmaTranslator, ctx))
  }

  implicit val funSpecToFunSpecTranslator: IrisTranslator[FunSpec, IFunSpec] = (g, ctx, _) => {
    assert(ctx.isDefined)
    val params = g.params.map { case (v, t) => (v.translate, t.translate) }

    val cardinalityParams: Map[String, HCardType] = (g.pre.sigma.chunks ++ g.post.sigma.chunks).flatMap({
      case PointsTo(loc, offset, value) => None
      case Block(loc, sz) => None
      case SApp(pred, args, tag, Var(name)) => Some(name, HCardType(pred))
      case _ => throw TranslationException("ERR: Expecting all predicate applications to be abstract variables")
    }).toMap

    val newGamma = g.gamma(ctx.get.env).translate ++ cardinalityParams

    // We quantify over all universals, ignoring the type of function arguments
    val specUniversal = g.universals.map(v => (v.translate.translate(progVarToSpecVar, ctx), newGamma(v.name)))
    val specExistential = g.existentials().map(v => (v.translate.translate(progVarToSpecVar, ctx), newGamma(v.name))).toSeq

    val pre = g.pre.translate(assertionTranslator, ctx)
    val post = g.post.translate(assertionTranslator, ctx)
    IFunSpec(g.name, params.map(x => (x._1.translate(progVarToSpecVar, ctx), x._2)),
      specUniversal.toSeq, specExistential, pre, post, helper = true)
  }

  implicit val goalToFunSpecTranslator: IrisTranslator[Goal, IFunSpec] = (g, ctx, _) => {
    assert(ctx.isDefined)
    val params = g.programVars.map(v => (v.translate, g.gamma(v).translate))

    val cardinalityParams: Map[String, HCardType] = (g.pre.sigma.chunks ++ g.post.sigma.chunks).flatMap({
      case PointsTo(loc, offset, value) => None
      case Block(loc, sz) => None
      case SApp(pred, args, tag, Var(name)) => Some(name, HCardType(pred))
      case _ => throw TranslationException("ERR: Expecting all predicate applications to be abstract variables")
    }).toMap

    val newGamma = g.gamma.translate ++ cardinalityParams

    // We quantify over all universals, ignoring the type of function arguments
    val universals = g.pre.vars ++ g.programVars
    val specUniversal = universals.map(v => (v.translate.translate(progVarToSpecVar, ctx), newGamma(v.name)))
    val specExistential = g.existentials.map(v => (v.translate.translate(progVarToSpecVar, ctx), newGamma(v.name))).toSeq

    val pre = g.pre.translate(assertionTranslator, ctx)
    val post = g.post.translate(assertionTranslator, ctx)
    IFunSpec(g.fname, params.map(x => (x._1.translate(progVarToSpecVar, ctx), x._2)), specUniversal.toSeq, specExistential, pre, post)
  }

  implicit val predicateTranslator: IrisTranslator[InductivePredicate, IPredicate] = (predicate, ctx, _) => {
    assert(ctx.isDefined)

    class IPredicateTranslation extends PredicateTranslation[IPureAssertion, ISpatialAssertion, HType, IPredicateClause, IPredicate] {
      override def translatePredicateParamType(predName: String, ty: SSLType): HType = ty match {
        case CardType => HCardType(predName)
        case _ => ty.translate
      }

      override def translateExpression(context: Map[Ident, HType])(expr: Expr): IPureAssertion = {
        val predCtx = Some(ProgramTranslationContext(ctx.get.env, ctx.get.proc, predicate.params.toMap, Map.empty, context))
        expr.translate(exprTranslator, predCtx).translate(toSpecExpr, predCtx)
      }

      override def translateHeaplets(context: Map[Ident, HType])(heaplets: List[Heaplet]): List[ISpatialAssertion] = {
        val predCtx = Some(ProgramTranslationContext(ctx.get.env, ctx.get.proc, predicate.params.toMap, Map.empty, context))
        heaplets.map(_.translate(heapleatTranslator, predCtx))
      }

      override def constructClause(pure: List[IPureAssertion], spatial: List[ISpatialAssertion], subConstructor: Map[String, CardConstructor]): IPredicateClause = {
        IPredicateClause(pure, spatial, subConstructor)
      }

      override def constructPred(name: Ident, params: List[(Ident, HType)], existentials: List[(Ident, HType)], clauses: Map[CardConstructor, IPredicateClause]): IPredicate = {
        IPredicate(name, params, existentials, clauses)
      }
    }
    new IPredicateTranslation().translatePredicate(ctx.get.env)(predicate)
  }

}
