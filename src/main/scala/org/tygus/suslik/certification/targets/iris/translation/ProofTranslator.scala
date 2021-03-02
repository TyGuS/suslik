package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HCardType, HLocType, HType, HUnknownType}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{ICardConstructor, IFunSpec, IPredicate, IPureAssertion, ISpecVar}
import org.tygus.suslik.certification.targets.iris.logic._
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.normalize_renaming
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.Statements.Load
import org.tygus.suslik.language.{Expressions, Ident, Statements}


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
                          renamings: Map[Ident, Ident],
                          pendingCall: Option[IFunSpec]
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

  def removeFromCoqContext(variables: List[Ident]): IProofContext = {
    val newCtx = coqTypingCtx.filterNot(v => variables.contains(v._1))
    this.copy(coqTypingCtx = newCtx)
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

  def withQueuedCall(fs: IFunSpec): IProofContext = this.copy(pendingCall = Some(fs))

  def unqueueCall(): (IFunSpec, IProofContext) = (pendingCall.get, this.copy(pendingCall = None))

  def withRenaming(ren: (Ident, Ident)): IProofContext = {
    val (from, to) = ren
    val s = Map(from -> to)
    def trueName(v: Ident): Ident = s.getOrElse(v, v)

    val newCoqTypingCtx = coqTypingCtx.map({ case (v, ty) => (trueName(v), ty) })
    val newVarMap = varMap.map { case (v, expr) => (trueName(v), expr.rename(s)) }
    val newRenamings = renamings.map{ case (from, to) => (from, trueName(to)) } ++ s

    val newCall = pendingCall match {
      case None => None
      case Some(call) => Some(call.rename(s))
    }

    this.copy(coqTypingCtx = newCoqTypingCtx, varMap = newVarMap, renamings = newRenamings, pendingCall = newCall)
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
  private val irisRet = "Ret"
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
      val irisHyps = IPatList(List(IPatDestruct(pureIntro ++ spatialIntro), IIdent(irisPost)))
      val intro = IIntros(coqHyps, irisHyps)

      val universals = spec.specUniversal.map({ case (v, t) => (v.name, t) })
      val existentials = spec.specExistential.map({ case (v, t) => (v.name, t) })
      ctx = ctx withVariablesTypes universals.toMap
      ctx = ctx withVariablesTypes existentials.toMap

      val deferred: Deferred = (ctx: IProofContext) => {
        val instantiate = existentials.map({ case (v, _) => IExists(ctx resolveExistential v) })
        (List(IFindApply) ++ instantiate ++ List(IFinish), ctx)
      }

      val lobInduction = ILob(IIdent(irisSelf),
        spec.specUniversal.map({ case (v, _) => ICoqName(v.name) })
          ++ pureIntro.map(v => ICoqName(v.name))
          ++ List(ICoqName(irisPhi)))
      val steps = List(intro, IRewriteHyp, lobInduction, IBegin)
      Result(steps, List((Nil, Some(deferred), ctx)))

    case SuslikProofStep.Open(predApp, freshExists, freshParams, selectors) =>
      val ctx = clientCtx
      val app = predApp.translate(IrisTranslator.predAppTranslator, ctx.translationCtx)
      val appHyp = ctx.freshHypName()
      val appHypIdent = IIdent(appHyp)
      val pureHyp = IPure(appHyp + "_eqn")
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
            IOpenCard(pred, constructor, constructorExistentials, appHypIdent, pureHyp),
            IDestruct(appHypIdent, coqIntro, irisHyps)
          )
          val newCtx = ctx withVariablesTypes (existentials ++ constructorExistentials).toMap
          (immed, noDeferreds, newCtx)
      }
      Result(steps, childRules.toList)

    // TODO: actually implement
    case SuslikProofStep.Close(app, selector, _, freshExist) =>
      var ctx = clientCtx
      val ren = normalize_renaming(freshExist.map { case (Var(from), Var(to)) => (from, to) })
      val pred = clientCtx.predMap(app.pred)
      val cardVar = app.card.asInstanceOf[Var].name
      val tctx = clientCtx.baseTranslationContext.copy(hctx = pred.params.toMap)
      val translSelector = selector.translate.translate(IrisTranslator.toSpecExpr, Some(tctx))
      val (constructor, clause) = pred.clauses.find { case (_, cl) => cl.selector == translSelector }.get
      val existentials = pred.findExistentials(constructor)(clause).map( { case (name, ty) => (ren(name), ty) })
      val constructorArgs = constructor.constructorArgs.map(v => (ren(v), HCardType(pred.name)))
      ctx = ctx withVariablesTypes existentials.toMap
      ctx = ctx withVariablesTypes constructorArgs.toMap
      ctx = ctx withMappingBetween(cardVar,
        ICardConstructor(
          pred.name,
          pred.constructorName(constructor),
          constructorArgs.map { case (v, t) => ISpecVar(v, t) }
        ))
      val deferred : Deferred = (baseCtx: IProofContext) => {
        var ctx = baseCtx
        val unfold = IUnfold(pred, constructor)
        val existentialSteps = existentials.flatMap(v =>
          List(
            IPullOutExist,
            IExists(ctx.resolveExistential(v._1))))
        ctx = ctx removeFromCoqContext existentials.map(_._1)
        ctx = ctx removeFromCoqContext constructorArgs.map(_._1)
        (List (unfold) ++ existentialSteps ++ List(IFinish), ctx)
      }
      Result(List(), List((List(), Some(deferred), ctx)))

    case SuslikProofStep.AbduceCall(_, _, _, _, freshSub, _, f, _) =>
      var ctx = clientCtx
      val funSpec = ctx.specMap(f.name)
      val s = normalize_renaming(freshSub.map { case (Var(name_from), Var(name_to)) => (name_from, name_to) })
      val newSpec = funSpec.rename(s)
      ctx = ctx withQueuedCall(newSpec)
      Result(List(), List(withNoDeferreds(ctx)))

    case SuslikProofStep.Call(subst, Statements.Call(Var(funName), _, _)) =>
      var (spec, ctx) = clientCtx.unqueueCall()
      val isSelfCall = (funName == irisSelf)
      val applyName = if (isSelfCall) s""""$irisSelf"""" else s"${funName}_spec"
      val instantiate = spec.specUniversal.map { case (ISpecVar(name, _), _) => subst.getOrElse(Var(name), Var(name)) }
        .map(e => e.translate.translate(IrisTranslator.toSpecExpr, ctx.translationCtx))

      val retExistentials = spec.specExistential.map { case (v, _) => ICoqName(v.name) }
      val pureIntro = spec.post.phi.conjuncts.map(_ => IPure(ctx.freshHypName()))
      val spatialIntro = spec.post.sigma.heaplets.map(_ => IIdent(ctx.freshHypName()))
      val irisHyps = IPatDestruct(List(IPatDestruct(pureIntro), IPatDestruct(spatialIntro)))
      val pureInst = spec.pre.phi.conjuncts.length
      val spatialInst = spec.pre.sigma.heaplets.length

      val ret = ctx.freshHypName()
      // If we're self-calling, we destructed our precondition before doing iLob
      // On the other hand, if we're using a spec, the precondition is a single spatial assertion
      val apply = if (isSelfCall)
        IWpApply(applyName, instantiate, pureInst, spatialInst)
      else IWpApply(applyName, instantiate, 0, 1, applyLemma = true)
      // TODO: need to identify heaps for wp_apply by name?
      val steps = List(
        apply,
        IIntros(Seq(), IIdent(ret)),
        IDestruct(IIdent(ret), retExistentials, irisHyps),
        IEmp
      )
      ctx = ctx withVariablesTypes spec.specExistential.map{ case (v, t) => (v.name, t) }.toMap

      Result(steps, List(withNoDeferreds(ctx)))

    // TODO: actually implement
    case SuslikProofStep.SubstL(Var(from), to) =>
      val ctx = clientCtx withMappingBetween (from, to)
      Result(List(), List(withNoDeferreds(ctx)))

    case SuslikProofStep.SubstR(Var(from), to) =>
      val ctx = clientCtx withMappingBetween (from, to)
      Result(List(), List(withNoDeferreds(ctx)))


    case SuslikProofStep.Malloc(Var(ghostFrom), Var(ghostTo), Statements.Malloc(_, _, sz)) =>
      val newVar = (ghostTo, HLocType())
      var ctx = clientCtx
      ctx = ctx withVariablesTypes List(newVar).toMap
      ctx = ctx withMappingBetween(ghostFrom, ISpecVar(ghostTo, HLocType()))
      ctx = ctx withRenaming ghostFrom -> ghostTo
      val steps =  List (
        IMalloc(ICoqName(ghostTo), sz),
        IMovePure
        )
      Result(steps, List(withNoDeferreds(ctx)))

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
    case SuslikProofStep.NilNotLval(_) =>
//      val steps = vars.map { case Var(name) => INilNotVal(name, clientCtx.freshHypName() )}
      Result(List(), List(withNoDeferreds(clientCtx)))

//    case SuslikProofStep.PickArg(Var(from), to) =>
//      val newCtx = clientCtx withMappingBetween (from,to)
//      withNoOp(newCtx)

    case SuslikProofStep.PickCard(Var(from), to) =>
      var cardType = clientCtx.typingContext(from).asInstanceOf[HCardType]
      val predType = cardType.predType
      val pred = clientCtx.predMap(predType)
      val emptyConstr = pred.clauses.head._1
      val secondConstr = pred.clauses.toList(1)._1
      val cardExpr = to match {
        case Var(name) => ISpecVar(name, HCardType(predType))
        case Expressions.IntConst(v) if v == 0 =>
          ICardConstructor(predType, pred.constructorName(emptyConstr), List())
        case Expressions.BinaryExpr(Expressions.OpPlus, Var(name), Expressions.IntConst(v)) if v == 1 =>
          ICardConstructor(
            predType, pred.constructorName(secondConstr), List(
              ISpecVar(name, HCardType(predType))
            ))
      }
      val ctx = clientCtx withMappingBetween(from, cardExpr)
      withNoOp(ctx)

    /** Ignored rules */
    case SuslikProofStep.CheckPost(_, _, _)
         | SuslikProofStep.WeakenPre(_)
         | SuslikProofStep.HeapUnify(_)
         | SuslikProofStep.HeapUnifyUnfold(_, _, _)
         | SuslikProofStep.HeapUnifyPointer(_, _)
         | SuslikProofStep.StarPartial(_, _)
         | SuslikProofStep.FrameUnfold(_, _) =>
      withNoOp(clientCtx)
  }

  private def withNoDeferreds(ctx: IProofContext): (List[IProofStep], Option[Deferred], IProofContext) = (Nil, noDeferreds, ctx)

  def withNoOp(context: IProofContext): Result = Result(List(), List((Nil, None, context)))
}
