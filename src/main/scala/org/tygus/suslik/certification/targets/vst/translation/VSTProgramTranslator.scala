package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.Types
import org.tygus.suslik.certification.targets.vst.Types.{CoqIntValType, CoqPtrValType, VSTCType, VSTType}
import org.tygus.suslik.certification.targets.vst.logic.Expressions.{CLangExpr, ProofCExpr}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{Forward, ForwardIf, ValidPointer}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Subst, SubstVar, Var}
import org.tygus.suslik.language.{IntType, LocType, SSLType}
import org.tygus.suslik.certification.targets.vst.clang.Statements.{CCall, CElif, CFree, CIf, CLoadInt, CLoadLoc, CMalloc, CSkip, CWriteInt, CWriteLoc, StatementStep}
import org.tygus.suslik.certification.targets.vst.translation.VSTProgramTranslator.VSTProgramContext
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.VSTClientContext
import org.tygus.suslik.language.Statements.{Call, Free, Load, Malloc, Store}
import org.tygus.suslik.logic.{Block, Gamma, Heaplet, PointsTo, SApp}

import scala.collection.immutable.Queue

object VSTProgramTranslator {

  case class VSTProgramContext
  (
    typing_context: Map[String, VSTCType]
  ) extends ClientContext[StatementStep] {
    def with_new_variable(to: String, variable_type: VSTCType) =
      VSTProgramContext(typing_context ++ Map(to -> variable_type))
  }

  def empty_context = VSTProgramContext(Map())

}

class VSTProgramTranslator extends Translator[SuslikProofStep, StatementStep, VSTProgramContext] {
  type Deferred = Evaluator.Deferred[StatementStep, VSTProgramContext]
  private val no_deferreds: Option[Deferred] = None
  private val no_ops : List[StatementStep] = List()

  def single_child_result_of(a: List[StatementStep], b : (List[StatementStep], Option[Deferred], VSTProgramContext)) = Result(a, List(b))

  def no_child_result_of(a: List[StatementStep]) : Result[StatementStep, VSTProgramContext] = Result(a, List())



  def with_no_op(implicit context: VSTProgramTranslator.VSTProgramContext): Result[StatementStep, VSTProgramTranslator.VSTProgramContext] =
    Result(List(), List((Nil, None, context)))


  def to_heap(typing_context: Map[String, VSTCType], chunks: List[Heaplet]) = {
    val gamma: Gamma = typing_context.map({
      case (name, CoqPtrValType) => (Var(name), LocType)
      case (name, CoqIntValType) => (Var(name), IntType)
    })
    val block_map = chunks.flatMap({
      case Block(Var(ptr), sz) => Some((ptr, sz))
      case _ => None
    }).toMap
    val free_ptrs = chunks.flatMap({
      case PointsTo(Var(loc), 0, value) if !(block_map contains loc) => Some((loc, 1))
      case _ => None
    }).toMap
    (block_map ++ free_ptrs).map {
      case (ptr, sz) =>
      val types : Array[Option[VSTCType]] = Array.fill(sz)(None)
      chunks.foreach({
        case PointsTo(Var(ptr_prime), offset, value) if ptr_prime == ptr =>
          types.update(offset, value.getType(gamma).flatMap({
            case IntType => Some(CoqIntValType)
            case LocType => Some(CoqPtrValType)
            case _ => None
          }))
        case _ => ()
      })
      (ptr, types.map(_.get).toList)
    }
  }

  def translate_type(tpe: SSLType): VSTCType = tpe match {
    case IntType => CoqIntValType
    case LocType => CoqPtrValType
  }

  override def translate(value: SuslikProofStep, clientContext: VSTProgramTranslator.VSTProgramContext): Result[StatementStep, VSTProgramTranslator.VSTProgramContext] = {
    implicit val ctx: VSTProgramTranslator.VSTProgramContext = clientContext
    value match {
      case SuslikProofStep.NilNotLval(_)
           | SuslikProofStep.CheckPost(_, _)
           | SuslikProofStep.Pick(_, _)
           | SuslikProofStep.Close(_, _, _, _)
           | SuslikProofStep.StarPartial(_, _)
           | SuslikProofStep.PickCard(_, _)
           | SuslikProofStep.PickArg(_, _)
           | SuslikProofStep.AbduceCall(_, _, _, _, _, _, _, _)
           | SuslikProofStep.HeapUnify(_)
           | SuslikProofStep.HeapUnifyUnfold(_, _, _)
           | SuslikProofStep.HeapUnifyPointer(_, _)
           | SuslikProofStep.FrameUnfold(_, _)
           | SuslikProofStep.WeakenPre(_)
           | SuslikProofStep.PureSynthesis(_, _)
           | SuslikProofStep.SubstL(_, _)
           | SuslikProofStep.SubstR(_, _) => with_no_op
      case SuslikProofStep.Init(goal) =>
        val new_typing_context =
          ctx.typing_context ++ goal.gamma.flatMap({ case (Var(name), lType) => lType match {
              case IntType => Some((name, CoqIntValType))
              case LocType => Some((name, CoqPtrValType))
              case _ => None
            }})
        val new_context = VSTProgramContext(new_typing_context)
        single_child_result_of(no_ops, (Nil, no_deferreds, new_context))
      case SuslikProofStep.Open(pred, fresh_vars, sbst, selectors) =>
        val ops = CElif(selectors.map(v => ProofSpecTranslation.translate_expression(ctx.typing_context)(v).asInstanceOf[CLangExpr]))
        val children = selectors.map(_ => {
          (Nil, no_deferreds, ctx)
        })
        Result(List(ops), children)
      case SuslikProofStep.Branch(cond, bLabel) =>
        val ops = CIf(ProofSpecTranslation.translate_expression(ctx.typing_context)(cond).asInstanceOf[CLangExpr])
        val children = List((Nil, no_deferreds, ctx), (Nil, no_deferreds, ctx))
        Result(List(ops), children)
      case SuslikProofStep.Write(Store(Var(to), offset, base_expr)) =>
        val expr = ProofSpecTranslation.translate_expression(ctx.typing_context)(base_expr).asInstanceOf[CLangExpr]
        val op = expr.type_cexpr match {
          case Types.CoqPtrValType => CWriteLoc(to, expr, offset)
          case Types.CoqIntValType => CWriteInt(to, expr, offset)
        }
        single_child_result_of(List(op), (Nil, no_deferreds, ctx))
      case SuslikProofStep.Read(from_var, to_var, Load(Var(to),tpe, Var(from), offset)) =>
        val (op, variable_type) = tpe match {
          case IntType => (CLoadInt(to, from, offset), CoqIntValType)
          case LocType => (CLoadLoc(to, from, offset), CoqPtrValType)
        }
        val new_context = ctx with_new_variable(to, variable_type)
        single_child_result_of(List(op), (Nil, no_deferreds, new_context))
      case SuslikProofStep.Call(subst, Call(Var(fname), args, _)) =>
        val exprs = args.map(ProofSpecTranslation.translate_expression(ctx.typing_context)(_).asInstanceOf[CLangExpr])
        val op = CCall(fname, exprs)
        single_child_result_of(List(op), (Nil, no_deferreds, ctx))
      case SuslikProofStep.Free(Free(Var(name)), size) =>
        val op = CFree(name)
        single_child_result_of(List(op), (Nil, no_deferreds, ctx))
      case SuslikProofStep.Malloc(Var(_), Var(_), Malloc(Var(to), tpe, sz)) =>
        val new_context = ctx with_new_variable (to, translate_type(tpe))
        single_child_result_of(List(CMalloc(to, sz)), (Nil, no_deferreds, new_context))
      case SuslikProofStep.Inconsistency(label) => no_child_result_of(List(CSkip))
      case SuslikProofStep.EmpRule(label) => no_child_result_of(List(CSkip))
    }
  }
}