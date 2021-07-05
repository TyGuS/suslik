package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.Types
import org.tygus.suslik.certification.targets.vst.Types.{CoqCardType, CoqPtrValType, VSTType}
import org.tygus.suslik.certification.targets.vst.logic.Expressions.{ProofCBinaryExpr, ProofCCardinalityConstructor, ProofCExpr, ProofCIfThenElse, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{FormalSpecification, PureFormula, VSTPredicate}
import org.tygus.suslik.certification.targets.vst.logic.{Formulae, VSTProofStep}
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{AssertProp, AssertPropSubst, Exists, Forward, ForwardCall, ForwardEntailer, ForwardIf, ForwardIfConstructor, ForwardTernary, Free, Intros, IntrosTuple, Malloc, Rename, TentativeEntailer, UnfoldRewrite, ValidPointer}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Interpreter.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Interpreter}
import org.tygus.suslik.language.Expressions.{Expr, SubstVar, Var}
import org.tygus.suslik.language.{Expressions, Ident, SSLType, Statements}
import org.tygus.suslik.certification.targets.vst.translation.VSTProofInterpreter.{PendingCall, VSTClientContext, normalize_renaming}
import org.tygus.suslik.language.Statements.Load

object VSTProofInterpreter {

  /**
    * Represents a pending function call.
    *
    * @param function_name      name of the function being called.
    * @param args               arguments to function call
    * @param existential_params existential paramters in result of function call (will be introduced after calling function)
    * @param pre_conditions     pre-conditions to function
    * @param post_constraints   list of constraints enforced by function after execution
    */
  case class PendingCall(
                          function_name: String,
                          args: List[(String, VSTType)],
                          existential_params: List[(String, VSTType)],
                          pre_conditions: List[PureFormula],
                          post_constraints: List[PureFormula]
                        )

  /**
    * Represents the context needed to translate a proof into a VST proof
    *
    * @param pred_map            mapping of predicate names to their definitions
    * @param spec_map            mapping of function names to their specifications
    * @param coq_context         tracks the coq context as the proof progresses
    * @param existential_context tracks the existentials and types
    * @param variable_map        tracks values for existentials
    * @param call                function calls
    */
  case class VSTClientContext(
                               pred_map: Map[String, VSTPredicate],
                               spec_map: Map[String, FormalSpecification],
                               coq_context: Map[String, VSTType],
                               existential_context: Map[String, VSTType],
                               ghost_existential_context: Map[String, VSTType],
                               variable_map: Map[String, ProofCExpr],
                               renamings: Map[String, String],
                               call: Option[PendingCall]
                             ) extends ClientContext[VSTProofStep] {

    def is_existential_variable(from: String): Boolean = {
      existential_context.contains(from) || ghost_existential_context.contains(from)
    }

    def with_queued_call(suspended_call: PendingCall) = {
      VSTClientContext(pred_map, spec_map, coq_context, existential_context, ghost_existential_context, variable_map, renamings, Some(suspended_call))
    }

    def unqueue_call: (PendingCall, VSTClientContext) =
      (call.get, VSTClientContext(pred_map, spec_map, coq_context, existential_context, ghost_existential_context, variable_map, renamings, None))

    def typing_context: Map[String, VSTType] = coq_context ++ ghost_existential_context ++ existential_context

    def find_predicate_with_name(pred: Ident): VSTPredicate = pred_map(pred)

    def with_renaming(vl: Map[String,String]): VSTClientContext =
      vl.foldLeft(this)({case (ctx, map) => ctx.with_renaming(map)})

    def with_renaming(vl: (String, String)): VSTClientContext = {
      val (from, to) = vl
      val renaming = Map(from -> to)

      def true_name(vl: String) = renaming.getOrElse(vl, vl)

      val new_coq_context = coq_context.map({ case (name, ty) => (true_name(name), ty) })
      val new_ghost_context = ghost_existential_context.map({ case (name, ty) => (true_name(name), ty) })
      val new_existential_context = existential_context.map({ case (name, ty) => (true_name(name), ty) })
      val new_variable_map = variable_map.map {
        case (name, expr) => (true_name(name), expr.rename(renaming))
      }
      val new_call = call match {
        case None => None
        case Some(PendingCall(f_name, args, existential_params, pre_conditions, post_constraints)) =>
          Some(PendingCall(
            f_name, args.map(v => (true_name(v._1), v._2)),
            existential_params.map(v => (true_name(v._1), v._2)),
            pre_conditions.map(_.rename(renaming)),
            post_constraints.map(_.rename(renaming))
          ))
      }
      val new_renamings = renamings.map({case (from, to) => (from, true_name(to))}) ++ Map(from -> to)
      VSTClientContext(pred_map, spec_map, new_coq_context, new_existential_context, new_ghost_context, new_variable_map, new_renamings, new_call)
    }

    def with_existential_variables_of(variables: List[(String, VSTType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.toMap
      VSTClientContext(pred_map, spec_map, coq_context, existential_context ++ new_vars, ghost_existential_context, variable_map, renamings, call)
    }


    def without_existentials_of(variables: List[String]): VSTClientContext = {
      val new_existential_context = existential_context.filterNot(v => variables.contains(v._1))
      VSTClientContext(pred_map, spec_map, coq_context, new_existential_context, ghost_existential_context, variable_map, renamings, call)
    }

    def without_ghost_existentials_of(variables: List[String]): VSTClientContext = {
      val new_ghost_context = ghost_existential_context.filterNot(v => variables.contains(v._1))
      VSTClientContext(pred_map, spec_map, coq_context, existential_context, new_ghost_context, variable_map, renamings, call)
    }

    def resolve_existential(ident: Ident): ProofCExpr = {
      val true_name = renamings.getOrElse(ident, ident)
      variable_map(true_name).subst(variable_map)
    }

    def with_variables_of(variables: List[(String, VSTType)]): VSTClientContext = {
      // Note: translate_predicate_param_type maps val (containing ints) -> Z, and val (containing ptrs) -> val.
      // This is valid because the ssl_open_context tactic called at the start of a proof in VST will unwrap any
      // variable x in the context where ssl_is_valid_int(x) is known into a term of type Z (preserving the name - i.e (x : Z)).
      // As such, both ghost and program variables will correctly have type Z in the coq context (as the precondition for
      // specifications asserts that their values are valid ints).
      val new_vars: Map[String, VSTType] = variables.toMap
      VSTClientContext(pred_map, spec_map, coq_context ++ new_vars, existential_context, ghost_existential_context, variable_map, renamings, call)
    }

    def with_ghost_existentials_of(variables: List[(String, VSTType)]): VSTClientContext = {
      val new_vars: Map[String, VSTType] = variables.toMap
      VSTClientContext(pred_map, spec_map, coq_context, existential_context, ghost_existential_context  ++ new_vars, variable_map, renamings, call)
    }

    def with_mapping_between(from: String, to: Expr): VSTClientContext = {
      val target_type = typing_context.get(from)
      val to_expr = ProofSpecTranslation.translate_expression(typing_context)(to, target = target_type)
      with_mapping_between(from, to_expr)
    }

    def with_mapping_between(from: String, to_expr: ProofCExpr): VSTClientContext = {
      val subst = Map(from -> to_expr)
      val new_variable_map = variable_map.map({ case (name, vl) => (name, vl.subst(subst)) }) ++ subst
      val new_call = call.map({
        case PendingCall(f_name, args, eparams, preconds, postconds) =>
          PendingCall(f_name, args, eparams, preconds.map(v => v subst subst), postconds.map(v => v subst subst))
      })
      VSTClientContext(pred_map, spec_map, coq_context, existential_context, ghost_existential_context, new_variable_map, renamings, new_call)
    }

  }

  object VSTClientContext {
    def make_context(pred_map: Map[String, VSTPredicate], spec_map: Map[String, FormalSpecification]): VSTClientContext =
      VSTClientContext(pred_map, spec_map, Map(), Map(), Map(), Map(), Map(), None)
  }

  def normalize_renaming(renaming: Map[String, String]) = {
    var old_mapping = renaming
    var mapping = old_mapping.map(v => (v._1, renaming.getOrElse(v._2, v._2)))
    while(mapping != old_mapping) {
      old_mapping = mapping
      mapping = mapping.map(v => (v._1, renaming.getOrElse(v._2, v._2)))
    }
    mapping
  }

}

case class VSTProofInterpreter(spec: FormalSpecification) extends Interpreter[SuslikProofStep, VSTProofStep, VSTProofInterpreter.VSTClientContext] {
  type Deferred = Evaluator.Deferred[VSTProofStep, VSTClientContext]
  type Result = Interpreter.Result[VSTProofStep, VSTClientContext]

  var contains_free: Boolean = false
  var contains_malloc: Boolean = false

  private val no_deferreds: Option[Deferred] = None

    private def with_no_deferreds(ctx: VSTClientContext) : (List[VSTProofStep], Option[Deferred], VSTClientContext) = (Nil, no_deferreds, ctx)

    def with_no_op(context: VSTClientContext): Result = Result(List(), List((Nil, None, context)))

  def unwrap_val_type(ty: VSTType): VSTType = ty match {
    case Types.CoqPtrValType => Types.CoqPtrValType
    case Types.CoqIntValType => Types.CoqZType
    case v => v
  }

  override def interpret(value: SuslikProofStep, clientContext: VSTClientContext): Result = {
    value match {
      /** Initialization */
      case SuslikProofStep.Init(goal) =>
        var ctx = clientContext
        val program_vars = spec.c_params.toList.map { case (name, ty) => (name, unwrap_val_type(ty: VSTType)) }
        val ghost_vars = spec.formal_params.toList.map { case (name, ty) => (name, unwrap_val_type(ty)) }
        val existentials = spec.existensial_params
        ctx = ctx with_variables_of program_vars
        ctx = ctx with_variables_of ghost_vars
        ctx = ctx with_existential_variables_of existentials
        val deferreds: Deferred = (ctx: VSTClientContext) => {
          val steps: List[VSTProofStep] = existentials.map(v => Exists(ctx resolve_existential v._1))
          val new_ctx = ctx.without_existentials_of (existentials.map(_._1))
          (steps ++ (if (steps.nonEmpty) {
            List(TentativeEntailer)
          } else {
            List()
          }), new_ctx)
        }
        Result(List(), List((Nil, Some(deferreds), ctx)))

      /** Branching rules */
      case SuslikProofStep.Branch(cond) =>
        val cont = with_no_deferreds(clientContext)
        Result(List(ForwardIf), List(cont, cont))

      /** Call handling */
      case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) =>
        // Abduce call does two things
        //  - Adds a set of ghost existential variables (the parameters of the function) to the context
        //  - sets a pending function call on the context
        // (After the abduce call has ended, we can eliminate the ghost existential variables, and use deferreds to do so)
        var ctx = clientContext
        val fun_spec = ctx.spec_map(f.name)
        val renaming = normalize_renaming(freshSub.map { case (Var(name_from), Var(name_to)) => (name_from, name_to) })

        val post_constraints = fun_spec.postcondition.spatial_constraints.flatMap({
          case Formulae.CSApp(pred, args, card) =>
              val predicate = ctx.pred_map(pred)
              val param_map = predicate.params.zip(args).map({case ((name, _), (expr, _)) => (name, expr.rename(renaming))}).toMap
               predicate.pure_constraints.map(v => v.subst(param_map))
          case _ => List()
        })
        val function_params = fun_spec.params.map((pair) => (renaming(pair._1), pair._2))
        val function_result_existentials = fun_spec.existensial_params.map { case (name, ty) => (renaming(name), ty) }
        val function_preconds = fun_spec.precondition.pure_constraints.map(_.rename(renaming))
        val suspended_call = PendingCall(f.name, function_params, function_result_existentials, function_preconds, post_constraints)
        ctx = ctx with_ghost_existentials_of function_params
        ctx = ctx with_queued_call suspended_call
        // Use deferred to remove (translation-only) existentials produced by abduce-call
        val deferred = (ctx: VSTClientContext) => {
          (List(), ctx without_ghost_existentials_of function_params.map(_._1))
        }
        Result(List(), List((List(), Some(deferred), ctx)))

      case SuslikProofStep.Call(subst, call) =>
        // retreive call from ctx
        var (call, ctx) = clientContext.unqueue_call
        // resolve arguments to function call
        val call_args = call.args map (v => ctx.resolve_existential(v._1))
        val steps = {
          // assert and solve pure precondition for call
          val pre_steps = call.pre_conditions.map(v => AssertProp(v))
          pre_steps ++ List(
            // run call rule
            ForwardCall(call_args),
          ) ++
          // tentative entailer for complex calls
            (if (call.function_name != spec.name) {
              List(TentativeEntailer)
            } else {List()}) ++
            // intro existentials
            (if (call.existential_params.nonEmpty) {
              List(IntrosTuple(call.existential_params))
            } else {
              List()
            }) ++ (call.post_constraints.map(v => AssertProp(v)))
        }
        // update context to have existential variables produced by call
        ctx = ctx with_variables_of call.existential_params
        Result(steps, List((List(), None, ctx)))

      /** Proof Termination rules */
      case SuslikProofStep.EmpRule(label) =>
        Result(List(ForwardEntailer), List())

      case SuslikProofStep.Inconsistency(label) =>
        Result(List(ForwardEntailer), List())

      case SuslikProofStep.Write(stmt@Statements.Store(to, offset, e)) =>
        e match {
          // ternary expressions need to be special cased
          case e@Expressions.IfThenElse(cond, left, right) => // ternary
            val ternary_expr = ProofSpecTranslation.translate_expression(clientContext.typing_context)(e).asInstanceOf[ProofCIfThenElse]
            Result(List(ForwardTernary(ternary_expr), Forward), List(with_no_deferreds(clientContext)))
          case _ =>
          // otherwise, it is a normal write
            Result(List(Forward), List(with_no_deferreds(clientContext)))
        }

      case SuslikProofStep.Read(Var(ghost_from), Var(ghost_to), Load(to, _, from, offset)) =>
        val ctx = clientContext with_renaming ghost_from -> ghost_to
        val rename_step = Rename(ghost_from, ghost_to)
        val read_step = Forward
        Result(List(rename_step, read_step), List(with_no_deferreds(ctx)))

      case SuslikProofStep.Free(Statements.Free(Var(v)), size) =>
        this.contains_free = true
        val step = Free(v, size)
        Result(List(step), List(with_no_deferreds(clientContext)))

      case SuslikProofStep.Malloc(Var(ghostFrom), Var(ghostTo), Statements.Malloc(to, tpe, sz)) =>
        this.contains_malloc = true
        val new_var = (ghostTo, CoqPtrValType)
        var ctx = clientContext
        ctx = ctx with_variables_of List(new_var)
        ctx = ctx with_mapping_between (ghostFrom, ProofCVar(ghostTo, CoqPtrValType))
        ctx = ctx with_renaming ghostFrom -> ghostTo

        val steps = List(
          Malloc(sz),
          Intros(List(new_var))
        )
        Result(steps, List(with_no_deferreds(ctx)))

      /** Substitutions and renaming */
      case SuslikProofStep.Pick(from, to_expr) =>
        val new_context = clientContext with_mapping_between(from.name, to_expr)
        with_no_op(new_context)

      case SuslikProofStep.PureSynthesis(is_final, assignments) =>
        val new_context =
          assignments.foldLeft(clientContext)({ case (ctx, (from, to_expr)) => ctx with_mapping_between(from.name, to_expr) })
        with_no_op(new_context)

      case SuslikProofStep.PickArg(Var(from), to) =>
        val new_ctx = clientContext with_mapping_between (from,to)
        with_no_op(new_ctx)

      case SuslikProofStep.PickCard(Var(from), to) =>
        // Pick card is a hack - not sure what the best way to do this is.
        val card_type = clientContext.typing_context(from).asInstanceOf[CoqCardType]
        val pred_type = card_type.pred_type
        val predicate = clientContext.pred_map(pred_type)
        val empty_constructor = predicate.clauses.head._1
        val second_constructor = predicate.clauses.toList(1)._1
        val card_expr = to match {
          case Var(name) => ProofCVar(name, clientContext.typing_context(name))
          case Expressions.IntConst(v) if v == 0 =>
            ProofCCardinalityConstructor(pred_type, predicate.constructorName(empty_constructor), List())
          case Expressions.BinaryExpr(Expressions.OpPlus, Var(name), Expressions.IntConst(v)) if v == 1 =>
            ProofCCardinalityConstructor(
              pred_type, predicate.constructorName(second_constructor), List(
                ProofCVar(name, clientContext.typing_context(name))
              ))
        }
        var ctx = clientContext with_mapping_between (from, card_expr)
        with_no_op(ctx)

      case SuslikProofStep.SubstL(Var(from), to) =>
        // SubstL translated into `assert (from = to) as H; rewrite H in *`
        // No changes to context
        val ctx = clientContext with_mapping_between(from, to)
        val step =
          if (ctx.coq_context.contains(from)) {
            val from_type = clientContext.typing_context.get(from)
            val to_expr = ProofSpecTranslation.translate_expression(clientContext.typing_context)(to, target = from_type)
            List(AssertPropSubst(from, to_expr))
          } else {
            List()
          }
        Result(step, List((with_no_deferreds(ctx))))

      case SuslikProofStep.SubstR(Var(from), to) =>
        val from_type = clientContext.typing_context.get(from)
        val ctx = clientContext with_mapping_between(from, to)
        val to_expr = ProofSpecTranslation.translate_expression(clientContext.typing_context)(to, target = from_type)
        val deferred = if (ctx is_existential_variable from) {
          None
        } else {
          Some((ctx: VSTClientContext) => {
            val step = AssertPropSubst(from, to_expr)
            (List(step), ctx)
          })
        }
        Result(List(), List((List(), deferred, ctx)))

      /** Predicate folding/unfolding */
      case SuslikProofStep.Close(app, selector, asn, fresh_exist) =>
        var ctx = clientContext
        val fresh_exist_renaming = normalize_renaming(fresh_exist.map({case (Var(from), Var(to)) => (from,to)}))
        val predicate_name = app.pred
        val cardinality_var = app.card.asInstanceOf[Var].name
        val close_args = app.args.map(ProofSpecTranslation.translate_expression(ctx.typing_context)(_))

        val predicate = clientContext.pred_map(predicate_name)
        val (constructor, predicate_clause) = predicate.clause_by_selector(selector)
        val existentials = predicate.findExistentials(constructor)(predicate_clause).map({
          case (name,ty) => (fresh_exist_renaming(name), ty)
        })
        val constructor_args = constructor.constructorArgs.map(v => ProofCVar(fresh_exist_renaming(v), CoqCardType(predicate.name)))
        ctx = ctx with_existential_variables_of existentials
        ctx = ctx with_ghost_existentials_of (constructor_args.map(v => (v.name, v.typ)))
        ctx = ctx with_mapping_between(cardinality_var, ProofCCardinalityConstructor(
            predicate.name,
            predicate.constructorName(constructor),
            constructor_args
          ))
        val deferred_steps = (base_ctx: VSTClientContext) => {
          var ctx = base_ctx
          val unfold_step = UnfoldRewrite(
            predicate.unfold_lemma_name(constructor),
            constructor_args.map(v => Some(ctx.resolve_existential(v.name))) // ++
            // close_args.map(v => Some(v.rename(ctx.renamings).subst(ctx.variable_map, recurse=false)))
          )
          val existential_steps = existentials.map(v => Exists(ctx.resolve_existential(v._1)))

          ctx = ctx without_existentials_of existentials.map(_._1)
          ctx = ctx without_ghost_existentials_of constructor_args.map(_.name)
          (List(unfold_step) ++ existential_steps ++ List(TentativeEntailer), ctx)
        }
        Result(List(), List((List(), Some(deferred_steps), ctx)))

      case SuslikProofStep.Open(pred, fresh_exists, fresh_params, selectors) =>
        // Open rules translated into forward_if. - { ... } - { ... } ... - { ... }
        //            each case branch intros two types of variables (and thus changes the coq context)
        //                 - existential variables in the predicate - i.e lseg x s a = lseg_card_1 a' => exists ..., _
        //                 - cardinality variables within the
        val existentials_sub = fresh_exists.map { case (var1, var2) => (var1.name, var2.name) }
        //val params_sub = fresh_params.map { case (var1: Var, var2: Var) => (var1.name, var2.name) }
        val card_variable = pred.card.asInstanceOf[Var].name
        val predicate_name = pred.pred
        val predicate = clientContext.find_predicate_with_name(predicate_name)
        val c_selectors = selectors.map(ProofSpecTranslation.translate_expression(clientContext.typing_context)(_))
        val clauses = predicate.clauses.toList.zip(c_selectors).map {
          case ((constructor, body), expr) =>
            val existentials = predicate.findExistentials(constructor)(body).map({
              case (name, ty) => ((existentials_sub(name), ty))
            })
            val constructor_arg_existentials =
              constructor.constructorArgs.map(existentials_sub(_)).map(v => (v, CoqCardType(predicate_name)))
            (constructor, constructor_arg_existentials, existentials, expr)
        }

        val branches = clauses.map {
          case (constructor, cons_intro_variables, intro_variables, selector) =>
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
          case (_, constructor_intro_gamma, intro_gamma, _) =>
            var ctx = clientContext
            ctx = ctx with_variables_of constructor_intro_gamma ++ intro_gamma
            (List(), no_deferreds, ctx)
        }
        Result(List(step), child_rules)

      /** Misc. facts */
      case SuslikProofStep.NilNotLval(vars) =>
        // NilNotLval translated into `assert_prop (is_valid_pointer (var)) for var in vars`
        // No changes to context
        val valid_pointer_rules = vars.map({ case Var(name) => ValidPointer(name) })
        Result(valid_pointer_rules, List(with_no_deferreds(clientContext)))

      /** Ignored rules */
      case SuslikProofStep.CheckPost(_, _, _)
           | SuslikProofStep.AbduceBranch(_)
           | SuslikProofStep.WeakenPre(_)
           | SuslikProofStep.HeapUnify(_)
           | SuslikProofStep.HeapUnifyUnfold(_, _, _)
           | SuslikProofStep.HeapUnifyPointer(_, _)
           | SuslikProofStep.StarPartial(_, _)
           | SuslikProofStep.FrameUnfold(_, _) =>
        with_no_op(clientContext)
    }
  }
}
