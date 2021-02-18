package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.Types.VSTType
import org.tygus.suslik.certification.targets.vst.logic.Expressions.ProofCExpr
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{FormalSpecification, VSTPredicate}
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{Exists, Forward, ForwardIf, ValidPointer}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.{Ident, SSLType}
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.VSTClientContext

import scala.collection.immutable.Queue

object VSTProofTranslator {

  case class VSTClientContext(
                               pred_map: Map[String, VSTPredicate],
                               coq_context: Map[String, VSTType],
                               existential_context: Map[String, VSTType],
                               variable_map: Map[String, ProofCExpr]
                             ) extends ClientContext[VSTProofStep] {

    def with_existential_variables_of(variables: List[(String, SSLType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.map({ case (name, ty) => (name, ProofSpecTranslation.translate_predicate_param_type(ty)) }).toMap
      VSTClientContext(pred_map, coq_context, existential_context ++ new_vars, variable_map)
    }

    def resolve_existential(ident: Ident) : ProofCExpr = ???

    def with_variables_of(variables: List[(String, SSLType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.map({ case (name, ty) => (name, ProofSpecTranslation.translate_predicate_param_type(ty)) }).toMap
      VSTClientContext(pred_map, coq_context ++ new_vars, existential_context, variable_map)
    }

    def with_mapping_between(from: String, to: Expr): VSTClientContext = {
      val to_expr = ProofSpecTranslation.translate_expression(coq_context)(to)
      VSTClientContext(pred_map, coq_context, existential_context, variable_map ++ Map(from -> to_expr))
    }

  }

  object VSTClientContext {
    def make_context(pred_map: Map[String, VSTPredicate]): VSTClientContext =
      VSTClientContext(pred_map, Map(), Map(), Map())
  }
}
case class VSTProofTranslator(spec: FormalSpecification) extends Translator[SuslikProofStep, VSTProofStep, VSTProofTranslator.VSTClientContext] {
    type Deferred = Evaluator.Deferred[VSTProofStep, VSTClientContext]
    type Result = Translator.Result[VSTProofStep, VSTClientContext]
    private val no_deferreds: Option[Deferred] = None

    private def with_no_deferreds(ctx: VSTClientContext) : (Option[Deferred], VSTClientContext) = (no_deferreds, ctx)

    def with_no_op(context: VSTClientContext): Result = Result(List(), List((None, context)))

    override def translate(value: SuslikProofStep, clientContext: VSTClientContext): Result = {
      value match {
        /** Initialization */
        case SuslikProofStep.Init(goal) =>
          val program_vars = goal.programVars.map(v => (v.name, goal.gamma(v)))
          var ctx = clientContext with_variables_of program_vars
          val existential_params = goal.existentials.map(v => (v.name, goal.gamma(v))).toList
          ctx = ctx with_existential_variables_of existential_params
          val existentials = spec.existensial_params
          val deferreds : Deferred = (ctx: VSTClientContext) => {
            val steps : List[VSTProofStep] = existentials.map(v => Exists(ctx resolve_existential v._1)).toList
            (steps, ctx)
          }
          Result(List(), List((Some(deferreds), ctx)))

        /** Branching rules */
        case SuslikProofStep.Branch(cond, bLabel) =>
          val cont = with_no_deferreds(clientContext)
          Result(List(ForwardIf), List(cont, cont))

        /** Call handling */
        case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) => ???
        case SuslikProofStep.Call(subst, call) => ???

        /** Proof Termination rules */
        case SuslikProofStep.EmpRule(label) => ???
        case SuslikProofStep.Inconsistency(label) => ???

        case SuslikProofStep.Write(stmt) =>
          Result(List(Forward), List(with_no_deferreds(clientContext)))
        case SuslikProofStep.Read(from, to, operation) => ???
        case SuslikProofStep.Free(stmt, size) => ???
        case SuslikProofStep.Malloc(ghostFrom, ghostTo, stmt) => ???

        /** Substitutions and renaming */
        case SuslikProofStep.Pick(from, to_expr) =>
          val new_context = clientContext with_mapping_between(from.name, to_expr)
          with_no_op(new_context)
        case SuslikProofStep.PureSynthesis(is_final, assignments) =>
          val new_context =
            assignments.foldLeft(clientContext)({case (ctx, (from, to_expr)) => ctx with_mapping_between(from.name, to_expr)})
          with_no_op(new_context)
        case SuslikProofStep.PickArg(from, to) => ???
        case SuslikProofStep.PickCard(from, to) => ???
        case SuslikProofStep.SubstL(from, to) => ???
        case SuslikProofStep.SubstR(from, to) => ???

        /** Predicate folding/unfolding */
        case SuslikProofStep.Close(app, selector, asn, fresh_exist) => ???
        case SuslikProofStep.Open(pred, fresh_vars, sbst, selectors) => ???

        /** Misc. facts */
        case SuslikProofStep.NilNotLval(vars) =>
          val valid_pointer_rules = vars.map({ case Var(name) => ValidPointer(name) })
          Result(valid_pointer_rules, List(with_no_deferreds(clientContext)))

        /** Ignored rules */
        case SuslikProofStep.CheckPost(_, _)
             | SuslikProofStep.WeakenPre(_)
             | SuslikProofStep.HeapUnify(_)
             | SuslikProofStep.HeapUnifyPointer(_, _)
             | SuslikProofStep.StarPartial(_, _)
             | SuslikProofStep.FrameUnfold(_, _) =>
          with_no_op(clientContext)
      }
    }
  }
