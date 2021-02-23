package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions._
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HCardType, HIntSetType, HIntType, HLocType, HType, HUnknownType}
import org.tygus.suslik.certification.targets.iris.logic.Assertions._
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.translation.{CardConstructor, PredicateTranslation}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.{Call, Load, Malloc, Store}
import org.tygus.suslik.language.{CardType, Ident, IntSetType, IntType, LocType, SSLType}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic._

trait IrisTranslator[From, To] {
  def translate(value: From, ctx: Option[TranslationContext] = None): To
}

object IrisTranslator {
  case class TranslatorException(msg: String) extends Exception(msg)

  implicit val binOpTranslator: IrisTranslator[BinOp, HBinOp] = (value, _) => value match {
    case OpPlus => HOpPlus
    case OpMinus => HOpMinus
    case OpMultiply => HOpMultiply
    case OpEq | OpBoolEq => HOpEq
    case OpLeq => HOpLe
    case OpLt => HOpLt
    case _ => ???
  }

  implicit val overloadedBinOpTranslator: IrisTranslator[OverloadedBinOp, HBinOp] = (value, _) => value match {
    case OpOverloadedEq => HOpEq
    case OpOverloadedLeq => HOpLe
    case OpOverloadedPlus => HOpUnion
    case OpOverloadedStar => HOpMultiply
    case _ => ???
  }

  implicit val paramTranslator: IrisTranslator[(Var, SSLType), HProgVar] = (el, _) => el._1.translate(progVarTranslator)

  implicit val unopTranslator: IrisTranslator[UnOp, HUnOp] = (value, _) => value match {
    case OpNot => HOpNot
    case OpUnaryMinus => HOpUnaryMinus
  }

  implicit val exprTranslator: IrisTranslator[Expr, HExpr] = (expr, ctx) => {
    def visit(expr: Expr): HExpr = expr match {
      case Var(name) => HProgVar(name)
      case IntConst(v) => HLitInt(v)
      case LocConst(v) =>
        HLitLoc(v)
      case BoolConst(v) => HLitBool(v)
      case SetLiteral(elems) => HSetLiteral(elems.map(_.translate(exprTranslator)))
      case UnaryExpr(op, arg) => HUnaryExpr(op.translate, visit(arg))
      // Hack for null-pointer comparison
      case BinaryExpr(OpEq, v:Var, IntConst(value)) if ctx.get.gamma.get(v).contains(LocType) && value == 0 =>
        HBinaryExpr(HOpEq, visit(v), HLitLoc(0))
      case BinaryExpr(op, left, right) => HBinaryExpr(op.translate, visit(left), visit(right))
      case IfThenElse(cond, t, f) => HIfThenElse(visit(cond), visit(t), visit(f))
      case OverloadedBinaryExpr(op, left, right) => HBinaryExpr(op.translate, visit(left), visit(right))
      case _ => ???
    }
    visit(expr)
  }

  implicit val progVarTranslator: IrisTranslator[Var, HProgVar] = (pv, _) => HProgVar(pv.name)
  implicit val progVarToSpecVar: IrisTranslator[HProgVar, ISpecVar] = (hv, _) => ISpecVar(hv.name)
  implicit val progVarToSpecQuantifiedValue: IrisTranslator[HProgVar, ISpecQuantifiedValue] = (pv, ctx) => {
    assert(ctx.isDefined)
    (pv, ctx.get.gamma(Var(pv.name)).translate) match {
      case (HProgVar(name), HLocType()) => ISpecQuantifiedValue(s"l${name}")
      case (HProgVar(name), _) => ISpecQuantifiedValue(s"v${name}")
    }
  }

  implicit val typeTranslator: IrisTranslator[SSLType, HType] = (value, _) => value match {
    case IntType => HIntType()
    case LocType => HLocType()
    case IntSetType => HIntSetType()
    case CardType => HUnknownType()
    case _ => ???
  }

  implicit val mallocTranslator: IrisTranslator[Malloc, HStore] =
    (stmt, _) => HStore(stmt.to.translate, HAllocN(HLitInt(stmt.sz), HLitUnit()))
  implicit val loadTranslator: IrisTranslator[Load, HLet] =
    (stmt, _) => {
      val baseVar = stmt.from.translate
      val fromAddr = if (stmt.offset == 0) baseVar else HBinaryExpr(HOpOffset, baseVar, HLitLoc(stmt.offset))
      HLet(stmt.to.translate, HLoad(fromAddr), HLitUnit())
    }
  implicit val storeTranslator: IrisTranslator[Store, HStore] =
    (stmt, _) => {
      val baseVar = stmt.to.translate
      val toAddr = if (stmt.offset == 0) baseVar else HBinaryExpr(HOpOffset, baseVar, HLitLoc(stmt.offset))
      HStore(toAddr, stmt.e.translate)
    }

  implicit val callTranslator: IrisTranslator[Call, HCall] = (stmt, _) => HCall(stmt.fun.translate, stmt.args.map(_.translate))

  implicit val phiTranslator: IrisTranslator[PFormula, IPureAssertion] = (f, ctx) => {
    assert(ctx.isDefined)
    IAnd(f.conjuncts.map(_.translate.translate(toSpecExpr, ctx)).toSeq)
  }

  // TODO: remove duplication between toSpecExpr and toSpecVal
  implicit val toSpecExpr: IrisTranslator[HExpr, IPureAssertion] = (expr, ctx) => {
    assert(ctx.isDefined)
    expr match {
      // Get the quantified value if it is quantified
      case v: HProgVar => ctx.get.pts.getOrElse(v, v.translate(progVarToSpecVar))
      case l: HLit => ISpecLit(l)
      case HBinaryExpr(op, left, right) => ISpecBinaryExpr(op, left.translate(toSpecExpr, ctx), right.translate(toSpecExpr, ctx))
      case HUnaryExpr(op, expr) => ISpecUnaryExpr(op, expr.translate(toSpecExpr, ctx))
      case HSetLiteral(elems) => ISetLiteral(elems.map(_.translate(toSpecExpr, ctx)))
      case _ => ???
    }
  }

  implicit val toSpecVal: IrisTranslator[HExpr, IPureAssertion] = (expr, ctx) => {
    assert(ctx.isDefined)
    expr match {
      // Get the quantified value if it is quantified
      // If it's a ghost, it has a non-value type (e.g. Z), so we have to make it into a value
      case v: HProgVar => ctx.get.pts.getOrElse(v, ISpecLit(new HLit(v.name)))
      case l: HLit => ISpecLit(l)
      case HBinaryExpr(op, left, right) => ISpecBinaryExpr(op, left.translate(toSpecVal, ctx), right.translate(toSpecVal, ctx))
      case HUnaryExpr(op, expr) => ISpecUnaryExpr(op, expr.translate(toSpecVal, ctx))
      case HSetLiteral(elems) => ISetLiteral(elems.map(_.translate(toSpecVal, ctx)))
      case _ => ???
    }
  }


  implicit val pointsToTranslator: IrisTranslator[PointsTo, IPointsTo] = (f, ctx) => {
    val base = f.loc.translate.translate(toSpecExpr, ctx)
    val loc = if (f.offset > 0) ISpecBinaryExpr(HOpOffset, base, ISpecLit(HLitOffset(f.offset))) else base
    // Sometimes we get PointsTo(Var(x), 0, LocConst(0)) when we should get an IntConst
    val valToTranslate = f.value match {
      case LocConst(v) if v == 0 => IntConst(0)
      case _ => f.value
    }
    val value = valToTranslate.translate.translate(toSpecVal, ctx)
    IPointsTo(loc, value)
  }

  implicit val predAppTranslator: IrisTranslator[SApp, IPredApp] = (pa, ctx) => {
    assert(ctx.isDefined)
    IPredApp(pa.pred, pa.args.map(_.translate.translate(toSpecExpr, ctx)), pa.card.translate.translate(toSpecExpr, ctx))
  }

  implicit val heapleatTranslator: IrisTranslator[Heaplet, ISpatialAssertion] = (h, ctx) => {
    assert(ctx.isDefined)
    h match {
      case pt:PointsTo => pt.translate(pointsToTranslator, ctx)
      case bl:Block => IBlock()
      case pa:SApp => pa.translate(predAppTranslator, ctx)
      case _ => ???
    }
  }

  implicit val sigmaTranslator: IrisTranslator[SFormula, ISpatialAssertion] = (f, ctx) => {
    IHeap(f.chunks.map(_.translate(heapleatTranslator, ctx)))
  }

  implicit val assertionTranslator: IrisTranslator[Assertion, IAssertion] = (f, ctx) => {
    assert(ctx.isDefined)
    IAssertion(f.phi.translate(phiTranslator, ctx), f.sigma.translate(sigmaTranslator, ctx))
  }

  implicit val goalToFunSpecTranslator: IrisTranslator[Goal, IFunSpec] = (g, ctx) => {
    assert(ctx.isDefined)
    val params = g.programVars.map(v => (v.translate, g.gamma(v).translate))

    // OLD: untyped universals and existentials
    //    val specUniversal = g.universals.map(_.translate.translate(progVarToSpecVar)).toSeq ++ quantifiedValues
    //    val specExistential = g.existentials.map(_.translate.translate(progVarToSpecVar)).toSeq

    // We "unwrap" every value to a l ↦ v form. quantifiedVal = v and takes the type of the value.
    val quantifiedValues = g.programVars.map(
      v => (v.translate.translate(progVarToSpecQuantifiedValue, Some(ctx.get)), g.gamma(v).translate)
    )
    // We quantify over all universals, ignoring the type of function arguments
    val quantifiedLocs = g.universals.map(v => (v.translate.translate(progVarToSpecVar),
      if(g.programVars.contains(v)) HUnknownType() else g.gamma(v).translate))
    val specUniversal = quantifiedLocs.toSeq ++ quantifiedValues
    val specExistential = g.existentials.map(v => (v.translate.translate(progVarToSpecVar), g.gamma(v).translate)).toSeq

    val pre = g.pre.translate(assertionTranslator, ctx)
    val post = g.post.translate(assertionTranslator, ctx)
    IFunSpec(g.fname, params.map(x => (x._1.translate(progVarToSpecVar), x._2)), specUniversal, specExistential, pre, post)
  }

  implicit val predicateTranslator: IrisTranslator[InductivePredicate, IPredicate] = (predicate, ctx) => {
    assert(ctx.isDefined)

    class IPredicateTranslation extends PredicateTranslation[IPureAssertion, ISpatialAssertion, HType, IPredicateClause, IPredicate] {
      override def translatePredicateParamType(predName: String, ty: SSLType): HType = ty match {
        case CardType => HCardType(predName)
        case _ => ty.translate
      }

      // TODO: should this be specExpr or specVal?
      override def translateExpression(context: Map[Ident, HType])(expr: Expr): IPureAssertion = expr.translate.translate(toSpecVal, ctx)

      override def translateHeaplets(context: Map[Ident, HType])(heaplets: List[Heaplet]): List[ISpatialAssertion] =
        heaplets.map(_.translate(heapleatTranslator, ctx))

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
