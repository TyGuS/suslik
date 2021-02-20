package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.Types
import org.tygus.suslik.certification.targets.vst.Types.{CoqCardType, VSTType}
import org.tygus.suslik.certification.targets.vst.logic.Expressions.{ProofCExpr, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{FormalSpecification, VSTPredicate}
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{AssertPropSubst, Entailer, Exists, Forward, ForwardEntailer, ForwardIf, ForwardIfConstructor, Rename, ValidPointer}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, SubstVar, Var}
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

    def typing_context: Map[String, VSTType] = coq_context

    def find_predicate_with_name(pred: Ident): VSTPredicate = pred_map(pred)

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

    def with_existential_variables_of(variables: List[(String, VSTType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.toMap
      VSTClientContext(pred_map, coq_context, existential_context ++ new_vars, variable_map)
    }

    def resolve_existential(ident: Ident) : ProofCExpr = variable_map(ident)

    def with_program_variables_of(variables: List[(String, VSTType)]): VSTClientContext = {
      // Note: translate_predicate_param_type maps val (containing ints) -> Z, and val (containing ptrs) -> val.
      // This is valid because the ssl_open_context tactic called at the start of a proof in VST will unwrap any
      // variable x in the context where ssl_is_valid_int(x) is known into a term of type Z (preserving the name - i.e (x : Z)).
      // As such, both ghost and program variables will correctly have type Z in the coq context (as the precondition for
      // specifications asserts that their values are valid ints).
      val new_vars: Map[String, VSTType] = variables.toMap
      VSTClientContext(pred_map, coq_context ++ new_vars, existential_context, variable_map)
    }

    def with_ghost_variables_of(variables: List[(String, VSTType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.toMap
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

  def unwrap_val_type(ty: VSTType) : VSTType = ty match {
    case Types.CoqPtrValType => Types.CoqPtrValType
    case Types.CoqIntValType => Types.CoqZType
    case v => v
  }

  override def translate(value: SuslikProofStep, clientContext: VSTClientContext): Result = {
      value match {
        /** Initialization */
        case SuslikProofStep.Init(goal) =>
          var ctx = clientContext
          val program_vars = spec.c_params.toList.map {case (name, ty) => (name, unwrap_val_type(ty : VSTType))}
          val ghost_vars = spec.formal_params.toList.map {case (name, ty) => (name, unwrap_val_type(ty))}
          val existential_params = spec.existensial_params.toList
          ctx = ctx with_program_variables_of program_vars
          ctx = ctx with_ghost_variables_of ghost_vars
          ctx = ctx with_existential_variables_of existential_params
          println(goal.pp)
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
        case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) =>

          ???
        case SuslikProofStep.Call(subst, call) => ???

        /** Proof Termination rules */
        case SuslikProofStep.EmpRule(label) =>

          Result(List(ForwardEntailer), List())
        case SuslikProofStep.Inconsistency(label) => ???

        case SuslikProofStep.Write(stmt) =>
          Result(List(Forward), List(with_no_deferreds(clientContext)))
        case SuslikProofStep.Read(Var(ghost_from), Var(ghost_to), Load(to, _, from, offset)) =>
          val ctx = clientContext with_renaming (ghost_from -> ghost_to)
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

        case SuslikProofStep.SubstL(Var(from), to) =>
          // SubstL translated into `assert (from = to) as H; rewrite H in *`
          // No changes to context
          val from_type = clientContext.typing_context(from)
          val to_expr = ProofSpecTranslation.translate_expression(clientContext.typing_context)(to, target = Some(from_type))
          val step = AssertPropSubst(from, to_expr)
          Result(List(step), List((with_no_deferreds(clientContext))))

        case SuslikProofStep.SubstR(from, to) => ???

        /** Predicate folding/unfolding */
        case SuslikProofStep.Close(app, selector, asn, fresh_exist) => ???
        case SuslikProofStep.Open(pred, fresh_exists, fresh_params, selectors) =>
          // Open rules translated into forward_if. - { ... } - { ... } ... - { ... }
          //            each case branch intros two types of variables (and thus changes the coq context)
          //                 - existential variables in the predicate - i.e lseg x s a = lseg_card_1 a' => exists ..., _
          //                 - cardinality variables within the
          val existentials_sub = fresh_exists.map { case (var1, var2) => (var1.name, var2.name)}
          val params_sub = fresh_params.map { case (var1 : Var, var2 : Var) => (var1.name, var2.name)}
          val card_variable = pred.card.asInstanceOf[Var].name
          val predicate_name = pred.pred
          val predicate = clientContext.find_predicate_with_name(predicate_name)
          val c_selectors = selectors.map(ProofSpecTranslation.translate_expression(clientContext.typing_context)(_))
          val clauses = predicate.clauses.toList.zip(c_selectors).map {
            case ((constructor, body), expr) =>
            val existentials = predicate.constructor_existentials(constructor).map({
              case (name, ty) => ((existentials_sub(name), ty))
            })
            val constructor_arg_existentials =
              constructor.constructor_args.map(existentials_sub(_)).map(v => (v, CoqCardType(predicate_name)))
            val renamed_body = body.rename(existentials_sub).rename(params_sub)
              (constructor, constructor_arg_existentials, existentials, renamed_body, expr)
          }

          val branches = clauses.map {
            case (constructor, cons_intro_variables, intro_variables, body, selector) =>
              val intro_names = intro_variables.map(_._1)
              val cons_intro_names = cons_intro_variables.map(_._1)
              ((constructor, cons_intro_names), selector, intro_names)
          }
          val step = ForwardIfConstructor(
            card_variable,
            predicate,
            branches
          )
          val child_rules = clauses.map {
            case (_, constructor_intro_gamma, intro_gamma, _, _) =>
              var ctx = clientContext
              ctx = ctx with_ghost_variables_of constructor_intro_gamma ++ intro_gamma
              (no_deferreds, ctx)
          }
          Result(List(step), child_rules)

        /** Misc. facts */
        case SuslikProofStep.NilNotLval(vars) =>
          // NilNotLval translated into `assert_prop (is_valid_pointer (var)) for var in vars`
          // No changes to context
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
