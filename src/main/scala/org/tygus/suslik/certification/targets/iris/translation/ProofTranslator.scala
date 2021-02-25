package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{IFunSpec, IPredicate}
import org.tygus.suslik.certification.targets.iris.logic.{IEmp, IInit, ILoad, IProofStep, IStore}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.{Ident, Statements}
import org.tygus.suslik.language.Statements.Load

case class IProofContext(
//                        predMap: Map[Ident, IPredicate],
//                        specMap: Map[Ident, IFunSpec]
                        ) extends ClientContext[IProofStep]

case class ProofTranslator(spec: IFunSpec) extends Translator[SuslikProofStep, IProofStep, IProofContext] {
  type Deferred = Evaluator.Deferred[IProofStep, IProofContext]
  type Result = Translator.Result[IProofStep, IProofContext]

  private val noDeferreds: Option[Deferred] = None

  private def withNoDeferreds(ctx: IProofContext) : (List[IProofStep], Option[Deferred], IProofContext) = (Nil, noDeferreds, ctx)

  def withNoOp(context: IProofContext): Result = Result(List(), List((Nil, None, context)))

  override def translate(value: SuslikProofStep, clientContext: IProofContext): Result = {
    value match {
      case SuslikProofStep.Init(goal) => Result(List(IInit), List(withNoDeferreds(clientContext)))

      case SuslikProofStep.EmpRule(_) => Result(List(IEmp), List())
      case SuslikProofStep.NilNotLval(vars) => withNoOp(clientContext)

      case SuslikProofStep.Read(Var(ghost_from), Var(ghost_to), Load(to, _, from, offset)) =>
        Result(List(ILoad), List(withNoDeferreds(clientContext)))

      case SuslikProofStep.Write(stmt@Statements.Store(to, offset, e)) =>
        Result(List(IStore), List(withNoDeferreds(clientContext)))

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
  }
}
