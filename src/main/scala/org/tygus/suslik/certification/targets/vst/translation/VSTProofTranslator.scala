package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.Types.VSTType
import org.tygus.suslik.certification.targets.vst.logic.Expressions.{ProofCExpr, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{FormalSpecification, VSTPredicate}
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{Entailer, Exists, Forward, ForwardEntailer, ForwardIf, Rename, ValidPointer}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.{Ident, SSLType}
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.VSTClientContext
import org.tygus.suslik.language.Statements.Load

import scala.collection.immutable.Queue

object VSTProofTranslator {

  case class VSTClientContext(
                               pred_map: Map[String, VSTPredicate],
                               coq_context: Map[String, VSTType],
                               existential_context: Map[String, VSTType],
                               variable_map: Map[String, ProofCExpr]
                             ) extends ClientContext[VSTProofStep] {

    def with_renaming(vl: (String, String)) : VSTClientContext = {
      val (from, to) = vl
      val renaming = Map(from -> to)
      def true_name(vl : String) = renaming.getOrElse(vl,vl)
      val new_coq_context = coq_context.map({case (name, ty) => (true_name(name), ty)})
      val new_existential_context = existential_context.map({case (name, ty) => (true_name(name), ty)})
      val new_variable_map = variable_map.map {
        case (name, expr) => (true_name(name), expr.rename(renaming))
      }
      VSTClientContext(pred_map, new_coq_context, new_existential_context, variable_map)
    }

    def with_existential_variables_of(variables: List[(String, SSLType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.map({ case (name, ty) => (name, ProofSpecTranslation.translate_predicate_param_type(ty)) }).toMap
      VSTClientContext(pred_map, coq_context, existential_context ++ new_vars, variable_map)
    }

    def resolve_existential(ident: Ident) : ProofCExpr = variable_map(ident)

    def with_program_variables_of(variables: List[(String, SSLType)]): VSTClientContext = {
      // Note: translate_predicate_param_type maps val (containing ints) -> Z, and val (containing ptrs) -> val.
      // This is valid because the ssl_open_context tactic called at the start of a proof in VST will unwrap any
      // variable x in the context where ssl_is_valid_int(x) is known into a term of type Z (preserving the name - i.e (x : Z)).
      // As such, both ghost and program variables will correctly have type Z in the coq context (as the precondition for
      // specifications asserts that their values are valid ints).
      val new_vars: Map[String, VSTType] = variables.map({ case (name, ty) => (name, ProofSpecTranslation.translate_predicate_param_type(ty)) }).toMap
      VSTClientContext(pred_map, coq_context ++ new_vars, existential_context, variable_map)
    }

    def with_ghost_variables_of(variables: List[(String, SSLType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.map({ case (name, ty) => (name, ProofSpecTranslation.translate_predicate_param_type(ty)) }).toMap
      VSTClientContext(pred_map, coq_context ++ new_vars, existential_context, variable_map)
    }


    def with_mapping_between(from: String, to: Expr): VSTClientContext = {
      val to_expr = ProofSpecTranslation.translate_expression(coq_context)(to)
      val subst = Map(from -> to_expr)
      val new_variable_map = variable_map.map({case (name, vl) => (name, vl.subst(subst))}) ++ subst
      VSTClientContext(pred_map, coq_context, existential_context, new_variable_map)
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
          val ghost_vars = goal.universalGhosts.map(v => (v.name, goal.gamma(v))).toList
          var ctx = clientContext with_program_variables_of program_vars
          ctx = ctx with_ghost_variables_of ghost_vars
          val existential_params = goal.existentials.map(v => (v.name, goal.gamma(v))).toList
          ctx = ctx with_existential_variables_of existential_params
          val existentials = spec.existensial_params
          val deferreds : Deferred = (ctx: VSTClientContext) => {
            val steps : List[VSTProofStep] = existentials.map(v => Exists(ctx resolve_existential v._1)).toList
            (steps ++ List(Entailer), ctx)
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
        case SuslikProofStep.EmpRule(label) =>

          Result(List(ForwardEntailer), List())
        case SuslikProofStep.Inconsistency(label) => ???

        case SuslikProofStep.Write(stmt) =>
          Result(List(Forward), List(with_no_deferreds(clientContext)))
        case SuslikProofStep.Read(Var(ghost_from), Var(ghost_to), Load(to, _, from, offset)) =>
          var ctx = clientContext with_renaming(ghost_from -> ghost_to)
          val rename_step = Rename(ghost_from, ghost_to)
          val read_step = Forward
          Result(List(rename_step, read_step), List(with_no_deferreds(ctx)))
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
