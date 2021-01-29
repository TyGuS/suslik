package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.targets.vst.clang.CTypes
import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CDataAt, CSApp, VSTHeaplet}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.Expressions._
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.{CoqCardType, CoqPtrType, VSTProofType}
import org.tygus.suslik.certification.targets.vst.logic.{Proof, ProofTerms, ProofTypes, VSTProofStep}
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.ProofTreePrinter
import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with
import org.tygus.suslik.certification.{CertTree, SuslikProofStep, ProofTree}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.Statements.{Call, Free, Load, Malloc}
import org.tygus.suslik.language.{Expressions, Ident, Statements}
import org.tygus.suslik.logic.SApp

import scala.collection.immutable.Map


object ProofTranslation {

  case class ProofRuleTranslationException(msg: String) extends Exception {
    override def toString: String = s"ProofRuleTranslationException(${msg})"
  }


  def translate_proof(
                       name: String,
                       predicates: List[VSTPredicate],
                       spec: ProofTerms.FormalSpecification,
                       root: CertTree.Node,
                       pre_cond: ProofTerms.FormalCondition,
                       post_cond: ProofTerms.FormalCondition
                     ): Proof = {
    val pred_map = predicates.map(v => (v.name, v)).toMap

    type FunSpec = (Ident, List[Ident], List[(Ident, VSTProofType)])

    /**
      * represents a unfold operation on a predicate
      */
    case class Unfold(
                       VSTPredicate: VSTPredicate,
                       cardinality: String,
                       args: List[(String, VSTProofType)],
                       existentials: List[(String, VSTProofType)],
                       new_equalities: Map[String, ProofCExpr],
                     )

    /** accumulating context used during proof translation
      *
      * @param gamma          typing context
      * @param functions      stack of functions being abduced during execution
      * @param queued_unfolds sequence of queued unfolds
      **/
    case class Context(post: List[(Ident, VSTProofType)],
                       gamma: Map[Ident, VSTProofType],
                       variable_map: Map[Ident, ProofCExpr],
                       functions: List[(Ident, List[Ident], List[(Ident, VSTProofType)])],
                       queued_unfolds: List[Unfold],
                       coq_context: Map[Ident, VSTProofType],
                       card_map: Map[Ident, ProofCExpr]
                      )


    def unify_expr(context: Map[Ident, Ident])(pure: ProofCExpr)(call: ProofCExpr): Map[Ident, Ident] =
      (pure, call) match {
        case (ProofCVar(name, _), ProofCVar(call_name, _)) => context + (name -> call_name)
        case (ProofCBoolConst(_), ProofCBoolConst(_)) => context
        case (ProofCIntConst(_, _), ProofCIntConst(_, _)) => context
        case (ProofCSetLiteral(elems, _), ProofCSetLiteral(call_elems, _)) =>
          elems.zip(call_elems).foldLeft(context)({ case (context, (expr, call_expr)) => unify_expr(context)(expr)(call_expr) })
        case (ProofCIfThenElse(cond, left, right), ProofCIfThenElse(call_cond, call_left, call_right)) =>
          var new_context = unify_expr(context)(cond)(call_cond)
          new_context = unify_expr(new_context)(left)(call_left)
          unify_expr(new_context)(right)(call_right)
        case (ProofCBinaryExpr(_, left, right), ProofCBinaryExpr(_, call_left, call_right)) =>
          val new_context = unify_expr(context)(left)(call_left)
          unify_expr(new_context)(right)(call_right)
        case (ProofCUnaryExpr(_, e), ProofCUnaryExpr(_, call_e)) =>
          unify_expr(context)(e)(call_e)
      }

    def unify_call_params(call_pre: ProofTerms.FormalCondition): List[(Ident, VSTProofType)] = {
      (pre_cond, call_pre) match {
        case (ProofTerms.FormalCondition(pure, spatial), ProofTerms.FormalCondition(call_pure, call_spatial)) =>
          def unify_pure(context: Map[Ident, Ident])(pure: ProofTerms.PureFormula)(call: ProofTerms.PureFormula): Map[Ident, Ident] = {
            (pure, call) match {
              case (ProofTerms.IsValidPointerOrNull(CVar(name)), ProofTerms.IsValidPointerOrNull(CVar(name1))) =>
                context + (name -> name1)
              case (ProofTerms.IsValidInt(CVar(name)), ProofTerms.IsValidInt(CVar(name1))) =>
                context + (name -> name1)
              case (ProofTerms.IsTrueProp(expr), ProofTerms.IsTrueProp(expr1)) =>
                unify_expr(context)(expr)(expr1)
              case (ProofTerms.IsTrue(expr), ProofTerms.IsTrue(expr1)) =>
                unify_expr(context)(expr)(expr1)
            }
          }

          def unify_spatial(context: Map[Ident, Ident])(pure: VSTHeaplet)(call: VSTHeaplet): Map[Ident, Ident] = {
            (pure, call) match {
              case (CDataAt(loc, elem_ty, count, elem), CDataAt(call_loc, call_elem_ty, call_count, call_elem)) =>
                unify_expr(unify_expr(context)(loc)(call_loc))(elem)(call_elem)
              case (CSApp(pred, args, card), CSApp(call_pred, call_args, call_card)) =>
                assert(pred == call_pred)
                unify_expr(args.zip(call_args).foldRight(context)({ case ((exp, call_exp), context) =>
                  unify_expr(context)(exp)(call_exp)
                }))(card)(call_card)
            }
          }

          var context = pure.zip(call_pure).foldLeft(Map[Ident, Ident]())({ case (context, (pure, call_pure)) => unify_pure(context)(pure)(call_pure) })
          context = spatial.zip(call_spatial).foldLeft(context)({ case (context, (pure, call_pure)) => unify_spatial(context)(pure)(call_pure) })
          spec.params.map({ case (name, ty) => (context(name), ty) })
      }
    }

    val initial_context: Context =
      Context(spec.existensial_params.toList, (
        spec.c_params.map({
          case (name, CTypes.CIntType) => (name, ProofTypes.CoqIntType)
          case (name, CTypes.CVoidPtrType) => (name, ProofTypes.CoqPtrType)
          case (name, CTypes.CUnitType) => ???
          //                  case (name, CTypes.) => (name, ProofTypes.CoqPtrType)
          //                  case (name, ty) => (name, CoqParamType(ty))
        }) ++
          spec.formal_params ++
          spec.existensial_params
        ).toMap, Map(), Nil, Nil,
        (
          spec.c_params.map({
            case (name, CTypes.CIntType) => (name, ProofTypes.CoqIntType)
            case (name, CTypes.CVoidPtrType) => (name, ProofTypes.CoqPtrType)
            case (name, CTypes.CUnitType) => ???
            //                  case (name, CTypes.) => (name, ProofTypes.CoqPtrType)
            //                  case (name, ty) => (name, CoqParamType(ty))
          }) ++
            spec.formal_params
          ).toMap,
        Map())

    def retrieve_typing_context: Context => Map[Ident, VSTProofType] = _.gamma

    def add_new_variables(new_params: Map[Ident, VSTProofType])(context: Context): Context = context match {
      case Context(post, old_params, ex_map, funs, ufs, cc, cm) => Context(post, old_params ++ new_params, ex_map, funs, ufs, cc, cm)
    }

    def add_new_coq_variables(new_params: Map[Ident, VSTProofType])(context: Context): Context = context match {
      case Context(post, old_params, ex_map, funs, ufs, cc, cm) => Context(post, old_params, ex_map, funs, ufs, cc ++ new_params, cm)
    }

    def pop_function(context: Context): (FunSpec, Context) = context match {
      case Context(post, old_params, ex_map, fun :: funs, ufs, cc, cm) => (fun, Context(post, old_params, ex_map, funs, ufs, cc, cm))
      case _ => fail_with("Function called without prior abduce call")
    }

    def push_function(fun_spec: FunSpec)(context: Context): Context = context match {
      case Context(post, old_params, ex_map, old_funs, ufs, cc, cm) => Context(post, old_params, ex_map, fun_spec :: old_funs, ufs, cc, cm)
    }

    def push_unfolding(context: Context)(unfolded_expr: Unfold, new_equalities: Map[String, ProofCExpr]): Context =
      context match {
        case Context(post, gamma, variable_map, functions, queued_unfolds, cc, cm) =>
          Context(post, gamma, variable_map, functions, unfolded_expr :: queued_unfolds, cc, cm)
      }

    def record_variable_assignment(name: String, expr: Expr)(context: Context): Context = {
      // when recording a mapping of a pointer, force any int constants to be pointers (suslik doesn't always place them in loc_consts)
      val translated = ProofSpecTranslation.translate_expression(context.gamma)(expr)
      val result = (context.gamma.get(name), translated) match {
        case (Some(CoqPtrType), ProofCIntConst(value, _)) => ProofCIntConst(value, true)
        case (Some(ty), ProofCSetLiteral(elems, None)) => ProofCSetLiteral(elems, Some(ty))
        case (_, translated) => translated
      }
      val mapping = Map(name -> result)
      val variable_map = context.variable_map.map({ case (name, expr) => (name, expr.subst(mapping)) })
      Context(context.post, context.gamma, (variable_map ++ mapping), context.functions, context.queued_unfolds, context.coq_context, context.card_map)
    }

    def record_variable_assignment_raw(name: String, expr: ProofCExpr)(context: Context): Context = {
      // when recording a mapping of a pointer, force any int constants to be pointers (suslik doesn't always place them in loc_consts)
      val mapping = Map(name -> expr)
      val variable_map = context.variable_map.map({ case (name, expr) => (name, expr.subst(mapping)) })
      Context(context.post, context.gamma, (variable_map ++ mapping), context.functions, context.queued_unfolds, context.coq_context, context.card_map)
    }

    def record_variable_assignment_card(name: String, expr: ProofCExpr)(context: Context) =
      Context(context.post, context.gamma, (context.variable_map), context.functions, context.queued_unfolds, context.coq_context, context.card_map ++ Map(name -> expr))


    /**
      * Updates context to account for renaming induced by a mapping
      *
      * @param mapping a mapping encoding a renaming of variables (ASSUMED TO BE RENAMING VARIABLES to VARIABLES)
      * @param context the context
      * @return an updated context with variables renamed
      */
    def record_variable_mapping(mapping: Map[Var, Expr])(context: Context): Context = {
      val variable_mapping = mapping.flatMap({ case (Var(old_name), Var(new_name)) => Some((old_name, new_name)) case _ => None })
      val expr_map = variable_mapping.flatMap({ case (name, to) => context.gamma.get(name).map(ty => (name, ProofCVar(to, ty))) })

      def update_map(map: Map[Ident, ProofCExpr]): Map[Ident, ProofCExpr] =
        map.map({ case (name, expr) => (variable_mapping.getOrElse(name, name), expr.subst(expr_map)) })

      def update_map_static(map: Map[Ident, ProofCExpr]): Map[Ident, ProofCExpr] =
        map.map({ case (name, expr) => (name, expr.subst(expr_map)) })

      val post = context.post.map({ case (ident, proofType) => (variable_mapping.getOrElse(ident, ident), proofType) })
      // Convert mapping to a Map[String,String] using assumption that all mappings are between variables
      // Then rename all terms in the context
      val new_params = context.gamma.map({ case (name, ty) => (variable_mapping.getOrElse(name, name), ty) })
      val new_funs = context.functions.map({ case (fun_name, args, existentials) =>
        (fun_name, args.map(arg => variable_mapping.getOrElse(arg, arg)), existentials)
      })
      val new_variable_map = update_map(context.variable_map)
      val new_card_map = update_map(context.card_map)
      val new_unfolds = context.queued_unfolds.map({
        case Unfold(predicate, cardinality, args, existentials, new_equalities) =>
          val new_cardinality = cardinality
          //          match {
          //            case ProofTerms.CardNull => ProofTerms.CardNull
          //            case ProofTerms.CardOf(args) =>  ProofTerms.CardOf(args.map({case (name) => variable_mapping.getOrElse(name,name)}))
          //          }
          val new_args = args.map({ case (name, ty) => (variable_mapping.getOrElse(name, name), ty) })
          val new_existentials = existentials.map({ case (name, ty) => (variable_mapping.getOrElse(name, name), ty) })
          val new_new_equalities = new_equalities.map({ case (name, expr) => (variable_mapping.getOrElse(name, name), expr.subst(expr_map)) })
          Unfold(predicate, new_cardinality, new_args, new_existentials, new_new_equalities)
      })
      val coq_context = context.coq_context.map({ case (name, ty) => (variable_mapping.getOrElse(name, name), ty) })
      Context(post, new_params, new_variable_map, new_funs, new_unfolds, coq_context, new_card_map)
    }

    /**
      * Translates a Suslik Read rule to a series of VST tactics implementing the same operation.
      *
      * A suslik read rule, such as Read (x -> y, y = *p) performs the following operations:
      *   - updates all instances of variable x with y
      *   - if y is used in the rest of the program, emits a read operation
      *
      * This then corresponds to the VST rules:
      *   - rename x (if defined) with y
      *   - if y used in rest of program, then:
      *      - first assert that the pointer being read from is non-null (VST idiosynracy)
      *      - emit a forward tactic to move over the operation
      */
    def handle_read_rule(rule: SuslikProofStep.Read, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.Read(_, subst, option) =>
        subst.toList match {
          case ::((Var(old_var), Var(new_var)), _) =>
            def is_variable_used_in_exp(variable: Ident)(expr: Expr): Boolean = expr match {
              case Var(name) => (name == variable)
              case const: Expressions.Const => false
              case Expressions.BinaryExpr(op, left, right) =>
                is_variable_used_in_exp(variable)(left) || is_variable_used_in_exp(variable)(right)
              case Expressions.OverloadedBinaryExpr(overloaded_op, left, right) =>
                is_variable_used_in_exp(variable)(left) || is_variable_used_in_exp(variable)(right)
              case Expressions.UnaryExpr(op, arg) => is_variable_used_in_exp(variable)(arg)
              case Expressions.SetLiteral(elems) => elems.exists(is_variable_used_in_exp(variable))
              case Expressions.IfThenElse(cond, left, right) =>
                is_variable_used_in_exp(variable)(cond) || is_variable_used_in_exp(variable)(left) || is_variable_used_in_exp(variable)(right)
            }

            def is_variable_used_in_proof(variable: Ident)(rule: ProofTree[SuslikProofStep]): Boolean = {
              def map_varaible(map: Map[Var, Expr]): Ident =
                map.get(Var(variable)).flatMap({ case Var(name) => Some(name) case _ => None }).getOrElse(variable)

              rule match {
                case ProofTree(SuslikProofStep.NilNotLval(_, vars), List(next)) => is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.CheckPost(_, _, _), List(next)) => is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.PickCard(_, _), List(next)) => is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.PickArg(_, _), List(next)) =>
                  val picked_variables = subst.toList.flatMap({ case (Var(froe), Var(toe)) => Some(toe) case _ => None }).toSet
                  (picked_variables.contains(variable)) || is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.Pick(_, subst), List(next)) =>
                  val picked_variables = subst.toList.flatMap({ case (Var(froe), Var(toe)) => Some(toe) case _ => None }).toSet
                  (picked_variables.contains(variable)) || is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.AbduceBranch(_, cond, _), List(ifTrue, ifFalse)) =>
                  is_variable_used_in_exp(variable)(cond) ||
                    is_variable_used_in_proof(variable)(ifTrue) ||
                    is_variable_used_in_proof(variable)(ifFalse)
                case ProofTree(SuslikProofStep.Write(_, Statements.Store(Var(tov), offset, e)), List(next)) =>
                  (tov == variable) || is_variable_used_in_exp(variable)(e) || is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.WeakenPre(_, unused), List(next)) => is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.EmpRule(_), List()) => false
                case ProofTree(SuslikProofStep.PureSynthesis(_, is_final, assignments), List(next)) =>
                  is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.Open(_, pred, _, heaplet,cases), children) =>
                  cases.zip(children).exists({ case (expr, rule) =>
                    is_variable_used_in_exp(variable)(expr) ||
                      is_variable_used_in_proof(variable)(rule)
                  })
                case ProofTree(SuslikProofStep.SubstL(_, map), List(next)) => is_variable_used_in_proof(map_varaible(map))(next)
                case ProofTree(SuslikProofStep.SubstR(_, map), List(next)) => is_variable_used_in_proof(map_varaible(map))(next)
                case ProofTree(SuslikProofStep.AbduceCall(_, new_vars, f_pre, callePost, call, freshSub, _, _, _), List(next)) =>
                  is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.HeapUnify(_, _), List(next)) => is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.HeapUnifyPointer(_, map), List(next)) => is_variable_used_in_proof(map_varaible(map))(next)
                case ProofTree(SuslikProofStep.FrameUnfold(_, h_pre, h_post), List(next)) => is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.Close(_, app, selector, asn, fresh_exist), List(next)) =>
                  is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.StarPartial(_, new_pre_phi, new_post_phi), List(next)) =>
                  is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.Read(_, map, Load(Var(toe), _, Var(frome), offset)), List(next)) =>
                  (frome == variable) || ((toe != variable) && is_variable_used_in_proof(variable)(next))
                case ProofTree(SuslikProofStep.Call(_, _, Call(_, args, _)), List(next)) =>
                  args.exists(is_variable_used_in_exp(variable)) ||
                    is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.Free(_, Free(Var(v)), _), List(next)) =>
                  (v == variable) || is_variable_used_in_proof(variable)(next)
                case ProofTree(SuslikProofStep.Malloc(_, map, Malloc(Var(toe), tpe, sz)), List(next)) =>
                  (toe != variable) && is_variable_used_in_proof(variable)(next)
              }
            }

            val new_context = record_variable_mapping(subst)(context)
            val rest = (retrieve_typing_context(context).get(old_var)) match {
              case Some(CoqPtrType) =>
                ProofTree(VSTProofStep.ValidPointerOrNull(new_var), List(translate_proof_rules(next)(new_context)))
              case _ => translate_proof_rules(next)(new_context)
            }
            if (is_variable_used_in_proof(new_var)(next)) {
              ProofTree(VSTProofStep.Rename(old_var, new_var), List(ProofTree(VSTProofStep.Forward, List(rest))))
            } else {
              ProofTree(VSTProofStep.Rename(old_var, new_var), List(rest))
            }
        }
    }

    /**
      * Translates a suslik Open Rule into the corresponding VST rules
      *
      * Does this by mapping each constructor of the opened predicate to a branch of the rule,
      * and then for each branch introducing the variables that it uses.
      */
    def handle_open_rule(rule: SuslikProofStep.Open, children: List[ProofTree[SuslikProofStep]], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.Open(_, SApp(predicate_name, args, _, Var(card_variable)), fresh_vars, _, cases) =>
        val pred = pred_map(predicate_name)
        val context_branches = pred.clauses.zip(cases.zip(children)).map({
          case ((constructor, clause), (expr, rule)) =>
            // each clause of the type introduces existentials
            val new_variables = pred.constructor_existentials(constructor).map({
              // rename existential variables if they have been assigned fresh variables
              case (variable, ty) => fresh_vars.get(Var(variable)).map({ case Var(new_name) => (new_name, ty) }).getOrElse((variable, ty))
            })
            val constructor_args = constructor.constructor_args.map(v => fresh_vars(Var(v)).name)
            val new_context_1 = add_new_variables(
              new_variables.toMap ++
                constructor_args.map(v => (v, CoqCardType(pred.name))).toMap
            )(context)
            val new_context_2 = add_new_coq_variables(new_variables.toMap ++
              constructor_args.map(v => (v, CoqCardType(pred.name))).toMap)(new_context_1)
            // val (args, constructor_args) = partition_cardinality_args(new_variables)()

            val card_value = ProofSpecTranslation.translate_cardinality(pred, constructor match {
              case ProofTerms.CardNull => ProofTerms.CardNull
              case ProofTerms.CardOf(args) => ProofTerms.CardOf(args.map(arg => fresh_vars.get(Var(arg)).map(_.name).getOrElse(arg)))
            })
            val new_context = record_variable_assignment_raw(card_variable, card_value)(new_context_2)
            val selector = ProofSpecTranslation.translate_expression(retrieve_typing_context(context))(expr)

            ((pred.constructor_name(constructor), constructor, constructor_args),
              selector,
              new_variables.map(_._1),
              translate_proof_rules(rule)(new_context))
        }).toList
        val branches = context_branches.map({ case (expr, selector, vars, _) => (expr, selector, vars) })
        val next = context_branches.map({ case (_, _, _, next) => next })
        ProofTree(VSTProofStep.ForwardIfConstructor(
          card_variable,
          predicate_name,
          branches
        ),
          next
        )
    }

    def handle_pick_rule(rule: SuslikProofStep.Pick, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.Pick(_, subst) =>
        val new_context = subst.map({ case (Var(name), expr) => (name, expr) }).foldRight(context)({
          case ((name, expr), context) => record_variable_assignment(name, expr)(context)
        })
        translate_proof_rules(next)(new_context)
    }

    def handle_pick_card_rule(rule: SuslikProofStep.PickCard, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.PickCard(_, subst) =>

        /** Given an expression representing a pick of a cardinality variable
          * returns the corresponding cardinality constructor
          *
          * i.e
          * _alpha_512 -> _alpha_514 + 1
          *
          * produces
          * (lseg_card_1 _alpha_514), [(_alpha_514, lseg_card)]
          * (i.e, the picked cardinality is that alpha_512 maps to lseg_card_1 _alpha_514, where _alpha_514 is a new existential variable)
          */
        def cardinality_expr_mapping_to_cardinality_map(base_expr: String)(expr: Expressions.Expr): (ProofCExpr, List[(Ident, VSTProofType)]) =
          expr match {
            case Var(name) =>
              context.gamma.get(name) match {
                case Some(ty) => (ProofCVar(name, ty), Nil)
                case None => (ProofCVar(name, context.gamma(base_expr)), List((name, context.gamma(base_expr))))
              }
            case rule@Expressions.BinaryExpr(Expressions.OpPlus, expr, Expressions.IntConst(_)) =>
              val (translated_expr, new_vars) = cardinality_expr_mapping_to_cardinality_map(base_expr)(expr)
              val pred_name = context.gamma(base_expr) match {
                case ProofTypes.CoqCardType(pred_type) => pred_type
              }
              val predicate = pred_map(pred_name)
              // NOTE: Assumes that all predicates have a 1-argument constructor
              (ProofCCardinalityConstructor(predicate.name, predicate.constructor_name(predicate.constructor_by_arg(1)), List(translated_expr)), new_vars)
          }

        val new_context = subst.map({ case (Var(name), expr) => (name, expr) }).foldRight(context)({
          case ((name, expr), context) =>
            val (translated_expr, new_vars) = cardinality_expr_mapping_to_cardinality_map(name)(expr)
            record_variable_assignment_card(name, translated_expr)(
              add_new_variables(new_vars.toMap)(context)
            )
        })
        translate_proof_rules(next)(new_context)
    }

    def handle_pick_arg_rule(rule: SuslikProofStep.PickArg, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.PickArg(_, subst) =>
        val new_context = subst.map({ case (Var(name), expr) => (name, expr) }).foldRight(context)({
          case ((name, expr), context) => record_variable_assignment(name, expr)(context)
        })
        translate_proof_rules(next)(new_context)
    }

    def handle_emp_rule(context: Context) = {
      def instantiate_existentials(existentials: List[(Ident, VSTProofType)])(then: ProofTree[VSTProofStep]): ProofTree[VSTProofStep] =
        existentials.foldRight(then)(
          (variable, next) =>
            ProofTree(VSTProofStep.Exists(context.variable_map.getOrElse(variable._1, ProofCVar(variable._1, variable._2))), List(next))
        )

      def add_evars(unfolds: List[Unfold])(then: ProofTree[VSTProofStep]): ProofTree[VSTProofStep] =
        unfolds.flatMap(unfold => unfold.new_equalities.map(v => ProofCVar(v._1, v._2.type_expr))).foldRight(then)({ case (proof_var, rest) =>
          if (context.coq_context.contains(proof_var.name)) {
            rest
          } else {
            ProofTree(VSTProofStep.IntroEvar(proof_var), List(rest))
          }
        })

      def unfold_predicates(then: ProofTree[VSTProofStep]): ProofTree[VSTProofStep] =
        context.queued_unfolds.foldLeft(then)(
          { case (next, unfold) =>
            val predicate: VSTPredicate = unfold.VSTPredicate
            unfold.new_equalities.foldRight(
              ProofTree(
                VSTProofStep.Unfold(
                  predicate,
                  unfold.VSTPredicate.params.length,
                  context.variable_map.getOrElse(unfold.cardinality, ProofCVar(unfold.cardinality, CoqCardType(predicate.name)))),
                List(unfold.existentials.foldRight(next)({ case ((variable, ty), next) => ProofTree(VSTProofStep.Exists(context.variable_map.getOrElse(variable, ProofCVar(variable, ty))), List(next)) })))
              : ProofTree[VSTProofStep]) ({
            case ((evar_name, evar_value), (next: ProofTree[VSTProofStep])) =>
              if (context.coq_context.contains(evar_name)) {
                next
              } else {
                ProofTree(VSTProofStep.InstantiateEvar(evar_name, context.card_map.getOrElse(evar_name, evar_value)), List(next))
              }
          })
          }
        )

      ProofTree(VSTProofStep.ForwardEntailer, List(
        add_evars(context.queued_unfolds)(
          instantiate_existentials(context.post)(
            context.post match { // If no existentials, only entailer will be at the end of the unfoldings
              case Nil =>
                context.queued_unfolds match {
                  case Nil => ProofTree(VSTProofStep.Qed, List())
                  case ::(_, _) => unfold_predicates(ProofTree(VSTProofStep.Entailer, List(ProofTree(VSTProofStep.Qed, List()))))
                }
              case ::(_, _) =>
                context.queued_unfolds match {
                  case Nil => ProofTree(VSTProofStep.Entailer, List(ProofTree(VSTProofStep.Qed, List())))
                  case ::(_, _) => ProofTree(VSTProofStep.Entailer, List(unfold_predicates(ProofTree(VSTProofStep.Entailer, List(ProofTree(VSTProofStep.Qed, List()))))))
                }
            }
          )
        )
      ))
    }

    def handle_pure_synthesis_rule(rule: SuslikProofStep.PureSynthesis, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.PureSynthesis(_, is_final, subst) =>
        val new_context = subst.map({ case (Var(name), expr) => (name, expr) }).foldRight(context)({
          case ((name, expr), context) => record_variable_assignment(name, expr)(context)
        })
        translate_proof_rules(next)(new_context)
    }

    def handle_heap_unify(rule: SuslikProofStep.HeapUnify, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.HeapUnify(_, _) =>
        //        val new_context = subst.map({case (Var(name), expr) => (name,expr) }).foldRight(context)({
        //          case ((name,expr), context) =>   record_variable_assignment(name,expr)(context)
        //        })
        translate_proof_rules(next)(context)
    }

    def handle_heap_unify_pointer(rule: SuslikProofStep.HeapUnifyPointer, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.HeapUnifyPointer(_, subst) =>
        val new_context = subst.map({ case (Var(name), expr) => (name, expr) }).foldRight(context)({
          case ((name, expr), context) => record_variable_assignment(name, expr)(context)
        })
        translate_proof_rules(next)(new_context)
    }

    def handle_substl_rule(rule: SuslikProofStep.SubstL, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.SubstL(_, map) =>
        map.toList.foldRight(translate_proof_rules(next)(context))({
          case ((Var(name), expr), next) =>
            ProofTree(VSTProofStep.AssertPropSubst(
              name,
              ProofSpecTranslation.translate_expression(retrieve_typing_context(context))(expr)),
              List(next))
        })
    }

    def handle_substr_rule(rule: SuslikProofStep.SubstR, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.SubstR(_, map) =>
        def apply_subst(context: Context)(map: List[(Var, Expr)]): ProofTree[VSTProofStep] =
          map match {
            case Nil => translate_proof_rules(next)(context)
            case ::((Var(old_name), Var(new_name)), rest) =>
              val new_context = record_variable_mapping(Map(Var(old_name) -> Var(new_name)))(context)
              ProofTree(VSTProofStep.Rename(old_name, new_name,

              ), List(apply_subst(new_context)(rest)))
            case ::((Var(name), expr), rest) =>
              val new_context = record_variable_assignment(name, expr)(context)
              apply_subst(new_context)(rest)
          }

        apply_subst(context)(map.toList)
    }

    def handle_abduce_call(rule: SuslikProofStep.AbduceCall, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.AbduceCall(_, new_vars, f_pre, callePost, Call(Var(fun), _, _), freshSub, _, _, _) =>
        var typing_context = retrieve_typing_context(context)
        f_pre.vars.foreach({ case Var(name) =>
          if (!typing_context.contains(name)) {
            typing_context = typing_context + (name -> CoqPtrType)
          }
        })
        val call_precond = ProofSpecTranslation.translate_assertion(typing_context)(f_pre)
        val call_args = unify_call_params(call_precond).map({ case (name, _) => name })
        val existentials = spec.existensial_params.toList.map({ case (name, ty) => (freshSub(Var(name)).name, ty) })
        var new_context = push_function((fun, call_args, existentials))(context)
        translate_proof_rules(next)(new_context)
    }

    def handle_nilnotnval_rule(rule: SuslikProofStep.NilNotLval, next: ProofTree[SuslikProofStep], context: Context) = rule match {
      case SuslikProofStep.NilNotLval(_, vars) =>
        vars.foldRight(translate_proof_rules(next)(context))({
          case (_@Var(name), rest) =>
            ProofTree(VSTProofStep.ValidPointer(
            name
          ), List(rest))
        })
    }

    def handle_abduce_branch_rule(rule: SuslikProofStep.AbduceBranch, ifTrue: ProofTree[SuslikProofStep], ifFalse: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.AbduceBranch(_, cond, _) =>
        ProofTree(VSTProofStep.ForwardIf, List(
          translate_proof_rules(ifTrue)(context),
          translate_proof_rules(ifFalse)(context)
        ))
    }

    def handle_call_rule(rule: SuslikProofStep.Call, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.Call(_, _, call) =>
        val ((fun, args, existentials), new_context_1) = pop_function(context)
        ProofTree(VSTProofStep.ForwardCall(args),
          existentials match {
            case Nil => List(translate_proof_rules(next)(new_context_1))
            case _ =>
              val new_context = add_new_coq_variables(existentials.toMap)(new_context_1)
              List(ProofTree(VSTProofStep.IntrosTuple(existentials), List(translate_proof_rules(next)(new_context))))
          })
    }

    def handle_write_rule(rule: SuslikProofStep.Write, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.Write(_, stmt) => ProofTree(VSTProofStep.Forward, List(translate_proof_rules(next)(context)))
    }

    def handle_free_rule(rule: SuslikProofStep.Free, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.Free(_, Free(Var(name)), size) => ProofTree(VSTProofStep.Free(name, size), List(translate_proof_rules(next)(context)))
    }

    def handle_close_rule(rule: SuslikProofStep.Close, next: ProofTree[SuslikProofStep], context: Context): ProofTree[VSTProofStep] = rule match {
      case SuslikProofStep.Close(_, app, o_selector, asn, fresh_exist) =>

        // Use application of of constructor to infer mapping of variables
        val predicate = pred_map(app.pred)
        val selector: ProofCExpr = ProofSpecTranslation.translate_expression(predicate.params.toMap)(o_selector)
        val (cardinality, clause) = predicate(selector)
        val substitution: Map[String, ProofCExpr] =
          predicate.params.zip(app.args).map({ case ((name, ty), arg) => (name, ProofSpecTranslation.translate_expression(context.gamma)(arg)) }).toMap

        val clause_existentials = predicate.find_existentials(cardinality)(clause).map({
          case (name, ty) => (fresh_exist(Var(name)).name, ty)
        })

        val card_equality: List[(String, ProofCExpr)] = List((app.card match {
          case Var(name) => name
        }, ProofSpecTranslation.translate_cardinality(predicate, cardinality)))

        /**
          * Given two equal expressions, attempts to extract a mapping on variables
          */
        def equal_variables_to_variable_mapping(expr_a: ProofCExpr)(expr_b: ProofCExpr) = (expr_a, expr_b) match {
          case (ProofCVar(var_a, a_ty), ProofCVar(var_b, b_ty)) =>
            if (context.gamma.contains(var_a)) {
              List((var_a, ProofCVar(var_b, b_ty)))
            }
            else {
              List((var_b, ProofCVar(var_a, a_ty)))
            }
          case (ProofCVar(var_a, _), b_expr) =>
            List((var_a, b_expr))
          case (a_expr, ProofCVar(var_b, _)) =>
            List((var_b, a_expr))
          case _ => List()
        }

        def extract_equalities(expr: ProofCExpr): List[(String, ProofCExpr)] = expr match {
          case ProofCBinaryExpr(ProofTerms.Expressions.ProofCOpAnd, left, right) =>
            extract_equalities(left) ++ extract_equalities(right)
          case ProofCBinaryExpr(op, left, right) => op match {
            case ProofTerms.Expressions.ProofCOpIntEq => equal_variables_to_variable_mapping(left)(right)
            case ProofTerms.Expressions.ProofCOpBoolEq => equal_variables_to_variable_mapping(left)(right)
            case ProofTerms.Expressions.ProofCOpSetEq => equal_variables_to_variable_mapping(left)(right)
            case ProofTerms.Expressions.ProofCOpPtrEq => equal_variables_to_variable_mapping(left)(right)
            case _ => List()
          }
          case _ => List()
        }

        //        val expr_equalities = clause.pure.map(_.subst(substitution)).flatMap(extract_equalities)

        val new_equalities = card_equality.toMap

        val args = cardinality.constructor_args.map(
          name => (fresh_exist(Var(name)).name, CoqCardType(predicate.name))
        )
        val unfolding = Unfold(predicate, app.card.asInstanceOf[Var].name, args, clause_existentials, new_equalities)
        val new_context = push_unfolding(context)(unfolding, new_equalities)
        val new_context_1 = record_variable_mapping(fresh_exist)(new_context) // record_variable_mapping(fresh_exist)(new_context)
        val new_context_2 = add_new_variables(clause_existentials.toMap)(new_context_1) // record_variable_mapping(fresh_exist)(new_context)

        translate_proof_rules(next)(new_context_2)
    }

    def handle_malloc_rule(rule: SuslikProofStep.Malloc, next: ProofTree[SuslikProofStep], context: Context) = rule match {
      case SuslikProofStep.Malloc(_, map, Malloc(Var(to_var), _, sz)) =>
        val new_context_1 =
          map.foldRight(
            add_new_variables(map.map({ case (Var(original), Var(name)) => (name, CoqPtrType) }))(context)
          )({ case ((Var(old_name), new_expr), context) => record_variable_assignment(old_name, new_expr)(context) })
        val new_context = add_new_coq_variables(Map(to_var -> CoqPtrType))(new_context_1)
        ProofTree(VSTProofStep.Malloc(sz),
          List(ProofTree(VSTProofStep.Intros(
            List((to_var, CoqPtrType))),
            List(translate_proof_rules(next)(new_context))
          )))
    }

    def translate_proof_rules(rule: ProofTree[SuslikProofStep])(context: Context): ProofTree[VSTProofStep] = {
      rule match {
        //          Branching rules
        case ProofTree(rule@SuslikProofStep.Open(_, SApp(_, _, _, Var(_)), _, _, _), children) => handle_open_rule(rule, children, context)
        case ProofTree(rule@SuslikProofStep.AbduceBranch(_, cond, _), List(ifTrue, ifFalse) ) => handle_abduce_branch_rule(rule, ifTrue, ifFalse, context)

        //          Read and write Operations
        case ProofTree(rule@SuslikProofStep.Write(_, _), List(next)) => handle_write_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.Read(_, subst, option), List(next)) => handle_read_rule(rule, next, context)

        //          Memory management rules
        case ProofTree(rule@SuslikProofStep.Free(_, Free(Var(_)), _), List(next)) => handle_free_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.Malloc(_, map, Malloc(Var(to_var), _, sz)), List(next)) => handle_malloc_rule(rule, next, context)

        //          Abduce call & Existentials
        case ProofTree(rule@SuslikProofStep.AbduceCall(_, _, _, _, Call(Var(_), _, _), _, _, _, _), List(next)) => handle_abduce_call(rule, next, context)
        case ProofTree(rule@SuslikProofStep.Pick(_, _), List(next)) => handle_pick_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.PureSynthesis(_, _, _), List(next)) => handle_pure_synthesis_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.PickCard(_, _), List(next)) => handle_pick_card_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.PickArg(_, _), List(next)) => handle_pick_arg_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.Call(_, _, _), List(next)) => handle_call_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.Close(_, _, _, _, _), List(next)) => handle_close_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.HeapUnify(_, _), List(next)) => handle_heap_unify(rule, next, context)
        case ProofTree(rule@SuslikProofStep.HeapUnifyPointer(_, _), List(next)) => handle_heap_unify_pointer(rule, next, context)


        //          Completion rule
        case ProofTree(SuslikProofStep.EmpRule(_), List()) => handle_emp_rule(context)

        //          Context changing rules
        case ProofTree(rule@SuslikProofStep.NilNotLval(_, _), List(next)) => handle_nilnotnval_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.SubstL(_, _), List(next)) => handle_substl_rule(rule, next, context)
        case ProofTree(rule@SuslikProofStep.SubstR(_, _), List(next)) => handle_substr_rule(rule, next, context)

        //          Ignored rules
        case ProofTree(SuslikProofStep.WeakenPre(_, unused), List(next)) => translate_proof_rules(next)(context)
        case ProofTree(SuslikProofStep.CheckPost(_, _, _), List(next)) => translate_proof_rules(next)(context)

        case ProofTree(SuslikProofStep.FrameUnfold(_, h_pre, h_post), List(next)) => translate_proof_rules(next)(context)


        case ProofTree(SuslikProofStep.StarPartial(_, new_pre_phi, new_post_phi), List(next)) => translate_proof_rules(next)(context)
      }
    }

    val simplified = SuslikProofStep.of_certtree(root)
    println(s"Suslik Proof:\n ${simplified.pp}")

    val vst_proof: ProofTree[VSTProofStep] = translate_proof_rules(simplified)(initial_context)

    Proof(name, predicates, spec, vst_proof, contains_free(simplified), contains_malloc(simplified))
  }

  def contains_free(proof: ProofTree[SuslikProofStep]): Boolean = proof.rule match {
    case SuslikProofStep.Free(_, stmt, size) => true
    case _ => proof.children.exists(contains_free)
  }

  def contains_malloc(proof: ProofTree[SuslikProofStep]): Boolean = proof.rule match {
    case SuslikProofStep.Malloc(_, map, stmt) => true
    case _ => proof.children.exists(contains_malloc)
  }

}
