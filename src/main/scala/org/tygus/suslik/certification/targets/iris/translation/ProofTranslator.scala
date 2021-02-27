package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HCardType, HType, HUnknownType}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{IFunSpec, IPredicate, IPureAssertion}
import org.tygus.suslik.certification.targets.iris.logic._
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.Statements.Load
import org.tygus.suslik.language.{Ident, Statements}


case class PendingCall(
                      functionName: Ident,
                      )

case class IProofContext(
                          var counter: Integer = 0,
                          baseTranslationContext: ProgramTranslationContext,
                          predMap: Map[Ident, IPredicate],
                          specMap: Map[Ident, IFunSpec],
                          coqTypingCtx: Map[Ident, HType],
                          varMap: Map[Ident, IPureAssertion],
                          renamings: Map[Ident, Ident]
                        ) extends ClientContext[IProofStep] {

  def freshHypName(): String = {
    counter += 1
    s"iH${counter}"
  }

  def translationCtx: Option[ProgramTranslationContext] = {
    Some(baseTranslationContext.copy(pts = Map.empty, hctx = typingContext))
  }

  def withVariablesTypes(variables: Map[Ident, HType]): IProofContext = {
    this.copy(coqTypingCtx = coqTypingCtx ++ variables)
  }

  def withMappingBetween(from: Ident, to: Expr): IProofContext = {
    val targetType = typingContext.get(from)
    val toExpr = to.translate.translate(IrisTranslator.toSpecExpr, translationCtx, targetType)
    withMappingBetween(from, toExpr)
  }

  def typingContext: Map[Ident, HType] = coqTypingCtx

  def withMappingBetween(from: Ident, to: IPureAssertion): IProofContext = {
    val s = Map(from -> to)
    val newVarMap = varMap.map({ case (name, vl) => (name, vl.subst(s)) }) ++ s
    this.copy(varMap = newVarMap)
  }

  def withRenaming(ren: (Ident, Ident)): IProofContext = {
    val (from, to) = ren
    val s = Map(from -> to)
    def trueName(v: Ident): Ident = s.getOrElse(v, v)

    val newCoqTypingCtx = coqTypingCtx.map({ case (v, ty) => (trueName(v), ty) })
    val newVarMap = varMap.map { case (v, expr) => (trueName(v), expr.rename(s)) }
    val newRenamings = renamings.map{ case (from, to) => (from, trueName(to)) } ++ s

    this.copy(coqTypingCtx = newCoqTypingCtx, varMap = newVarMap, renamings = newRenamings)
  }

  def resolveExistential(ident: Ident): IPureAssertion = {
    val trueName = renamings.getOrElse(ident, ident)
    varMap(trueName).subst(varMap)
  }
}

case class ProofTranslator(spec: IFunSpec) extends Translator[SuslikProofStep, IProofStep, IProofContext] {
  type Deferred = Evaluator.Deferred[IProofStep, IProofContext]
  type Result = Translator.Result[IProofStep, IProofContext]

  private val noDeferreds: Option[Deferred] = None

  private val irisPhi: String = "ϕ"
  private val irisPost: String = "Post"
  private val irisSelf: String = spec.fname

  override def translate(value: SuslikProofStep, clientCtx: IProofContext): Result =
    value match {
    case SuslikProofStep.Init(_) =>
      var ctx = clientCtx
      val coqHyps =
        spec.specUniversal.map({ case (v, _) => ICoqName(v.name) }) ++
          // Iris specific thing
          List(ICoqName("ϕ"))

      val pureIntro = spec.pre.phi.conjuncts.map(_ => IPure(ctx.freshHypName()))
      val spatialIntro = spec.pre.sigma.heaplets.map(_ => IIdent(ctx.freshHypName()))
      val irisHyps = IPatList(List(IPatDestruct(pureIntro ++ spatialIntro), IIdent("Post")))
      val intro = IIntros(coqHyps, irisHyps)

      val universals = spec.specUniversal.map({ case (v, t) => (v.name, t) })
      val existentials = spec.specExistential.map({ case (v, t) => (v.name, t) })
      ctx = ctx withVariablesTypes universals.toMap
      ctx = ctx withVariablesTypes existentials.toMap

      val deferred: Deferred = (ctx: IProofContext) => {
        val instantiate = existentials.map({ case (v, _) => IExists(ctx resolveExistential v) })
        (List(IFindApply) ++ instantiate ++ List(IFinish), ctx)
      }

      val lobInduction = ILob(IIdent(irisSelf), spec.specUniversal.map({ case (v, _) => ICoqName(v.name) }) ++ List(ICoqName(irisPhi)))
      val steps = List(intro, IRewriteHyp, lobInduction, IBegin)
      Result(steps, List((Nil, Some(deferred), ctx)))

    case SuslikProofStep.Open(predApp, freshExists, freshParams, selectors) =>
      val ctx = clientCtx
      val app = predApp.translate(IrisTranslator.predAppTranslator, ctx.translationCtx)
      val appHyp = ctx.freshHypName()
      val appHypIdent = IIdent(appHyp)
      val steps = List (
        // Give the heaplet containing the predicate application a fresh name, appHyp
        IRenameSelect(app.pp, appHypIdent),
        IIf(ICoqName(s"Cond_${appHyp}"))
      )
      val existentialsSub = freshExists.map { case (from, to) => (from.name, to.name) }
      val predName = predApp.pred
      val pred = ctx.predMap(predName)
      val childRules = pred.clauses.map {
        case (constructor, body) =>
          val existentials = pred.findExistentials(constructor)(body).map({ case (name, ty) => (existentialsSub(name), ty) })
          val constructorExistentials = constructor.constructorArgs.map(existentialsSub(_)).map(v => (v, HCardType(predName)))
          val coqIntro = existentials.map({ case (name, _) => ICoqName(name) })
          val pureIntro = body.pure.map(_ => IPure(ctx.freshHypName()))
          val spatialIntro = body.spatial.map(_ => IIdent(ctx.freshHypName()))
          val irisHyps = IPatDestruct(List(IPatDestruct(pureIntro), IPatDestruct(spatialIntro)))
          // Open and destruct the predicate appropriately in each clause
          val immed = List(
            IOpenCard(pred, constructor, constructorExistentials),
            IDestruct(appHypIdent, coqIntro, irisHyps)
          )
          val newCtx = ctx withVariablesTypes (existentials ++ constructorExistentials).toMap
          (immed, noDeferreds, newCtx)
      }
      Result(steps, childRules.toList)

//    // TODO: actually implement
//    case SuslikProofStep.Close(app, selector, _, freshExist) =>
//      Result(List(IDebug(value.pp)), List(withNoDeferreds(clientCtx)))

    // TODO: actually implement
    case SuslikProofStep.AbduceCall(_, precondition, _, _, freshSub, _, f, _) =>
      val ctx = clientCtx
      val funSpec = ctx.specMap(f.name)

      Result(List(IDebug(value.pp)), List(withNoDeferreds(ctx)))

    case s:SuslikProofStep.Call =>
      // TODO: actually implement
      Result(List(IDebug(s.pp)), List(withNoDeferreds(clientCtx)))

    // TODO: actually implement
    case s:SuslikProofStep.SubstL => Result(List(IDebug(s.pp)), List(withNoDeferreds(clientCtx)))
    case s:SuslikProofStep.SubstR => Result(List(IDebug(s.pp)), List(withNoDeferreds(clientCtx)))

    case SuslikProofStep.Free(_, sz) =>
      val steps = (0 until sz).map(_ => IFree).toList
      Result(steps, List(withNoDeferreds(clientCtx)))

    case SuslikProofStep.Branch(_, _) =>
      val cont = withNoDeferreds(clientCtx)
      val step = IIf(ICoqName(clientCtx.freshHypName()))
      Result(List(step), List(cont, cont))

    case SuslikProofStep.Pick(Var(fromName), to) =>
      val newCtx = clientCtx withMappingBetween(fromName, to)
      withNoOp(newCtx)

    case SuslikProofStep.PureSynthesis(_, assignments) =>
      val newCtx =
        assignments.foldLeft(clientCtx)({ case (ctx, (Var(fromName), to)) => ctx withMappingBetween(fromName, to) })
      withNoOp(newCtx)

    /** Statements */
    case SuslikProofStep.Read(Var(ghostFrom), Var(ghostTo), Load(to, _, from, offset)) =>
      val ctx = clientCtx withRenaming ghostFrom -> ghostTo
      val rename = IRename(ICoqName(ghostFrom), ICoqName(ghostTo))
      Result(List(rename, ILoad), List(withNoDeferreds(ctx)))

    case SuslikProofStep.Write(stmt@Statements.Store(to, offset, e)) =>
      Result(List(IStore), List(withNoDeferreds(clientCtx)))

    case SuslikProofStep.EmpRule(_) => Result(List(IEmp), List())
    case SuslikProofStep.NilNotLval(vars) => withNoOp(clientCtx) // TODO: add assumption


    /** Ignored rules */
    case SuslikProofStep.CheckPost(_, _)
         | SuslikProofStep.WeakenPre(_)
         | SuslikProofStep.HeapUnify(_)
         | SuslikProofStep.HeapUnifyUnfold(_, _, _)
         | SuslikProofStep.HeapUnifyPointer(_, _)
         | SuslikProofStep.StarPartial(_, _)
         | SuslikProofStep.FrameUnfold(_, _) =>
      withNoOp(clientCtx)

    case _ => ???
  }

  private def withNoDeferreds(ctx: IProofContext): (List[IProofStep], Option[Deferred], IProofContext) = (Nil, noDeferreds, ctx)

  def withNoOp(context: IProofContext): Result = Result(List(), List((Nil, None, context)))
}
