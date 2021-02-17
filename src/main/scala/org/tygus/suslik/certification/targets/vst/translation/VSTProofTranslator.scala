package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.targets.vst.Types.VSTType
import org.tygus.suslik.certification.targets.vst.logic.Expressions.ProofCExpr
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{Forward, ForwardIf, ValidPointer}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.SSLType
import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.VSTClientContext

import scala.collection.immutable.Queue

object VSTProofTranslator {

  case class VSTClientContext(
                               pred_map: Map[String, VSTPredicate],
                               coq_context: Map[String, VSTType],
                               variable_map: Map[String, ProofCExpr]
                             ) extends ClientContext[VSTProofStep] {

    def with_variables_of(variables: List[(String, SSLType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.map({ case (name, ty) => (name, ProofSpecTranslation.translate_predicate_param_type(ty)) }).toMap
      VSTClientContext(pred_map, coq_context ++ new_vars, variable_map)
    }

    def with_mapping_between(from: String, to: Expr): VSTClientContext = {
      val to_expr = ProofSpecTranslation.translate_expression(coq_context)(to)
      VSTClientContext(pred_map, coq_context, variable_map ++ Map(from -> to_expr))
    }

  }

  object VSTClientContext {
    def make_context(pred_map: Map[String, VSTPredicate]): VSTClientContext =
      VSTClientContext(pred_map, Map(), Map())
  }
}
class VSTProofTranslator extends Translator[SuslikProofStep, VSTProofStep, VSTProofTranslator.VSTClientContext] {
    type Deferred = Evaluator.Deferred[VSTProofStep, VSTClientContext]
    private val no_deferreds: Queue[Deferred] = Queue()

    private def with_no_deferreds(ctx: VSTClientContext) = (no_deferreds, ctx)

    def with_no_op(context: VSTClientContext): Result[VSTProofStep, VSTClientContext] = Result(List(), List((Queue(), context)))

    override def translate(value: SuslikProofStep, clientContext: VSTClientContext): Translator.Result[VSTProofStep, VSTClientContext] = {
      value match {
        case SuslikProofStep.NilNotLval(vars) =>
          val valid_pointer_rules = vars.map({ case Var(name) => ValidPointer(name) })
          Result(valid_pointer_rules, List(with_no_deferreds(clientContext)))
        case SuslikProofStep.CheckPost(prePhi, postPhi) =>
          with_no_op(clientContext)
        case SuslikProofStep.Pick(from, to_expr) =>
          val new_context = clientContext with_mapping_between(from.name, to_expr)
          with_no_op(new_context)
        case SuslikProofStep.Branch(cond, bLabel) =>
          val cont = with_no_deferreds(clientContext)
          Result(List(ForwardIf), List(cont, cont))
        case SuslikProofStep.Write(stmt) =>
          Result(List(Forward), List(with_no_deferreds(clientContext)))
        case SuslikProofStep.WeakenPre(unused) =>
          with_no_op(clientContext)
        case SuslikProofStep.EmpRule(label) => ???
        case SuslikProofStep.PureSynthesis(is_final, assignments) => ???
        case SuslikProofStep.Open(pred, fresh_vars, sbst, selectors) => ???
        case SuslikProofStep.SubstL(from, to) => ???
        case SuslikProofStep.SubstR(from, to) => ???
        case SuslikProofStep.Read(from, to, operation) => ???
        case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) => ???
        case SuslikProofStep.HeapUnify(subst) => ???
        case SuslikProofStep.HeapUnifyPointer(from, to) => ???
        case SuslikProofStep.FrameUnfold(h_pre, h_post) => ???
        case SuslikProofStep.Call(subst, call) => ???
        case SuslikProofStep.Free(stmt, size) => ???
        case SuslikProofStep.Malloc(ghostFrom, ghostTo, stmt) => ???
        case SuslikProofStep.Close(app, selector, asn, fresh_exist) => ???
        case SuslikProofStep.StarPartial(new_pre_phi, new_post_phi) => ???
        case SuslikProofStep.PickCard(from, to) => ???
        case SuslikProofStep.PickArg(from, to) => ???
        case SuslikProofStep.Init(goal) =>
          val program_vars = goal.programVars.map(v => (v.name, goal.gamma(v)))
          val ctx = clientContext with_variables_of program_vars
          val existentials = goal.existentials.toList.map(v => (v.name, goal.gamma(v)))
          with_no_op(ctx)
        case SuslikProofStep.Inconsistency(label) => ???
      }
    }
  }
