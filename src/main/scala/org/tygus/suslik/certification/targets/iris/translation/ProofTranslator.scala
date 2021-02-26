package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HType, HUnknownType}
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{IFunSpec, IPredicate, IPureAssertion}
import org.tygus.suslik.certification.targets.iris.logic._
import org.tygus.suslik.certification.targets.iris.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.Statements.Load
import org.tygus.suslik.language.{Ident, Statements}


case class IProofContext(
                          var counter: Integer = 0,
                          baseTranslationContext: ProgramTranslationContext,
                          predMap: Map[Ident, IPredicate],
                          specMap: Map[Ident, IFunSpec],
                          //                          irisSpatial: Map[Ident, ISpatialAssertion],
                          coqTypingCtx: Map[Ident, HType],
                          varMap: Map[Ident, IPureAssertion]
                        ) extends ClientContext[IProofStep] {

  def freshHypName(): String = {
    counter += 1
    s"iH${counter}"
  }

  def typingContext: Map[Ident, HType] = coqTypingCtx

  def withVariablesTypes(variables: Map[Ident, HType]): IProofContext = {
    this.copy(coqTypingCtx = coqTypingCtx ++ variables)
  }

  def withMappingBetween(from: Ident, to: Expr): IProofContext = {
    val targetType = typingContext.get(from)
    val translationCtx = Some(baseTranslationContext.copy(pts = Map.empty, hctx = typingContext))
    val toExpr = to.translate.translate(IrisTranslator.toSpecExpr, translationCtx, targetType)
    withMappingBetween(from, toExpr)
  }

  def withMappingBetween(from: Ident, to: IPureAssertion): IProofContext = {
    val s = Map(from -> to)
    val newVarMap = varMap.map({ case (name, vl) => (name, vl.subst(s)) }) ++ s
    this.copy(varMap = newVarMap)
  }

  def resolveExistential(ident: Ident): IPureAssertion = {
    // TODO: renamings
    val name = ident
    varMap(name).subst(varMap)
  }
}

case class ProofTranslator(spec: IFunSpec) extends Translator[SuslikProofStep, IProofStep, IProofContext] {
  type Deferred = Evaluator.Deferred[IProofStep, IProofContext]
  type Result = Translator.Result[IProofStep, IProofContext]

  private val noDeferreds: Option[Deferred] = None

  override def translate(value: SuslikProofStep, clientContext: IProofContext): Result = value match {
    case SuslikProofStep.Init(_) =>
      var ctx = clientContext
      val coqHyps =
        spec.specUniversal.map({ case (v, _) => ICoqName(v.name) }) ++
        spec.artificialUniversal.map({ case (v, _) => ICoqName(v.name) }) ++
        // We only use the loc_at / Z_at lemmas for rewriting, so we don't give them names
        spec.artificialUniversal.map({ case (v, _) => ICoqName("?") }) ++
        // Iris specific thing
        List(ICoqName("ϕ"))

      val pureIntro = spec.pre.phi.conjuncts.map(_ => IPure(ctx.freshHypName()))
      val spatialIntro = spec.pre.sigma.heaplets.map(_ => IIdent(ctx.freshHypName()))
      // TODO: add spatial assertions to context && rewrite them accordingly
      val irisHyps = IPatList(List(IPatDestruct(pureIntro ++ spatialIntro), IIdent("Post")))
      val intro = IIntros(coqHyps, irisHyps)

      // We modify the context to account for the loc_at / Z_at rewriting.
      // All the artificialUniversals that show up in the spec will be renamed by IBegin,
      // e.g. (l : val) with (lr : loc) (lr is artificial) will result in (l : loc).
      val typeOf = spec.artificialUniversal.map({ case (v, t) => (v.originalName, t) }).toMap
      val programVars = spec.specUniversal.map({ case (v, _) => (v.name, typeOf.getOrElse(v.name, HUnknownType())) })
      val existentials = spec.specExistential.map({ case (v, t) => (v.name, t) })
      ctx = ctx withVariablesTypes programVars.toMap
      ctx = ctx withVariablesTypes existentials.toMap

      val steps = List(intro, IBegin)

      val deferred: Deferred = (ctx: IProofContext) => {
        val instantiate = existentials.map({ case (v, _) => IExists(ctx resolveExistential v) })
        (List(IFindApply) ++ instantiate ++ List(IFinish), ctx)
      }

      Result(steps, List((Nil, Some(deferred), ctx)))

    case SuslikProofStep.Branch(_, _) =>
      val cont = withNoDeferreds(clientContext)
      val step = IIf(ICoqName(clientContext.freshHypName()))
      Result(List(step), List(cont, cont))

    case SuslikProofStep.Pick(Var(fromName), to) =>
      val newCtx = clientContext withMappingBetween(fromName, to)
      withNoOp(newCtx)

    case SuslikProofStep.PureSynthesis(_, assignments) =>
      val newCtx =
        assignments.foldLeft(clientContext)({ case (ctx, (Var(fromName), to)) => ctx withMappingBetween(fromName, to) })
      withNoOp(newCtx)

    /** Statements */
    case SuslikProofStep.Read(Var(ghost_from), Var(ghost_to), Load(to, _, from, offset)) =>
      Result(List(ILoad), List(withNoDeferreds(clientContext)))

    case SuslikProofStep.Write(stmt@Statements.Store(to, offset, e)) =>
      Result(List(IStore), List(withNoDeferreds(clientContext)))

    case SuslikProofStep.EmpRule(_) => Result(List(IEmp), List())
    case SuslikProofStep.NilNotLval(vars) => withNoOp(clientContext) // TODO: add assumption


    /** Ignored rules */
    case SuslikProofStep.CheckPost(_, _)
         | SuslikProofStep.WeakenPre(_)
         | SuslikProofStep.HeapUnify(_)
         | SuslikProofStep.HeapUnifyUnfold(_, _, _)
         | SuslikProofStep.HeapUnifyPointer(_, _)
         | SuslikProofStep.StarPartial(_, _)
         | SuslikProofStep.FrameUnfold(_, _) =>
      withNoOp(clientContext)

    case _ => ???
  }

  private def withNoDeferreds(ctx: IProofContext): (List[IProofStep], Option[Deferred], IProofContext) = (Nil, noDeferreds, ctx)

  def withNoOp(context: IProofContext): Result = Result(List(), List((Nil, None, context)))
}
