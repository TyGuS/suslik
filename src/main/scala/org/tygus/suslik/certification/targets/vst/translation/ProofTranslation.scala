package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.{CertTree, ProofRule}
import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CDataAt, CSApp, VSTHeaplet}
import org.tygus.suslik.certification.ProofRule.EmpRule
import org.tygus.suslik.certification.targets.vst.logic.ProofSteps.AssertPropSubst
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.Expressions.{ProofCBinaryExpr, ProofCBoolConst, ProofCCardinalityConstructor, ProofCExpr, ProofCIfThenElse, ProofCIntConst, ProofCSetLiteral, ProofCUnaryExpr, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{VSTPredicate, VSTPredicateClause}
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.{CoqCardType, CoqParamType, CoqPtrType, VSTProofType}
import org.tygus.suslik.certification.targets.vst.{Debug, State}
import org.tygus.suslik.certification.targets.vst.logic.{Formulae, Proof, ProofSteps, ProofTerms, ProofTypes}
import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Var}
import org.tygus.suslik.language.{Expressions, Ident, PrettyPrinting, Statements}
import org.tygus.suslik.language.Statements.{Call, Free, Load, Malloc, Skip, Store}
import org.tygus.suslik.logic.Preprocessor.{findMatchingHeaplets, sameLhs}
import org.tygus.suslik.logic.Specifications.SuspendedCallGoal
import org.tygus.suslik.logic.{Block, Heaplet, PFormula, PointsTo, SApp, SFormula, Specifications}
import org.tygus.suslik.synthesis.rules.LogicalRules.FrameBlock.profilesMatch
import org.tygus.suslik.synthesis.rules.LogicalRules.StarPartial.extendPure
import org.tygus.suslik.synthesis.rules.{DelegatePureSynthesis, FailRules, LogicalRules, OperationalRules, UnfoldingRules, UnificationRules}
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}

import scala.annotation.tailrec
import scala.collection.immutable.Map


object ProofTranslation {

  case class ProofRuleTranslationException(msg: String) extends Exception {
    override def toString: String = s"ProofRuleTranslationException(${msg})"
  }


  /**
    * Partitions a list of variables into those which correspond to cardinality arguments and those that do not.
    *
    *  - first list has new variables that do not correspond to cardinality arguments
    *  - second list has variables that correspond to cardinality arguments
    *
    * Explanation: cardinality arguments typically have names like _alpha_513,
    * but when introduced into the context in a suslik proof, they are given
    * fresh names such as _alpha_513x2.
    */
  def partition_cardinality_args(new_variables: List[(String, VSTProofType)])(card_args: List[String]) = {
    var seen_variables_set: Set[String] = Set()
    var contructor_map: Map[Ident, Ident] = Map()

    // partition variables into variables that correspond to arguments to the cardinality
    val args = new_variables.flatMap({
      case (variable_name, ty) =>
        if (!seen_variables_set.contains(variable_name)) {
          seen_variables_set = seen_variables_set + variable_name
          card_args find (name => variable_name.startsWith(name)) match {
            // if the any cardinality argument names are a prefix of the variable name, then this
            // variable is a fresh variable for that particular cardinality argument
            case Some(name) =>
              contructor_map = contructor_map + (name -> variable_name)
              None
            case None =>
              Some(variable_name)
          }
        } else {
          None
        }
    })
    (args, card_args.map(arg => contructor_map(arg)))
  }

  def translate_proof(
                       name: String,
                       predicates: List[VSTPredicate],
                       spec: ProofTerms.FormalSpecification,
                       root: CertTree.Node,
                       pre_cond: ProofTerms.FormalCondition
                     ): Proof = {
    val pred_map = predicates.map(v => (v.name, v)).toMap

    type FunSpec = (Ident, List[Ident], List[(Ident, VSTProofType)])

    /**
      * represents a unfold operation on a predicate
      */
    case class Unfold(
                       VSTPredicate: VSTPredicate,
                       cardinality: ProofTerms.CardConstructor,
                       args: List[(String, VSTProofType)],
                       existentials: List[(String,VSTProofType)]
                     )

    /** accumulating context used during proof translation
      *
      * @param gamma               typing context
      * @param functions           stack of functions being abduced during execution
      * @param queued_unfolds      sequence of queued unfolds
      * */
    case class Context(
                        post: List[(Ident, VSTProofType)],
                        gamma: Map[Ident, VSTProofType],
                        variable_map: Map[Ident, ProofCExpr],
                        functions: List[FunSpec],
                        queued_unfolds: List[Unfold]
                      )


    def unify_expr(context: Map[Ident, Ident])(pure: ProofCExpr)(call: ProofCExpr): Map[Ident, Ident] =
      (pure, call) match {
        case (ProofCVar(name, _), ProofCVar(call_name, _)) => context + (name -> call_name)
        case (ProofCBoolConst(_), ProofCBoolConst(_)) => context
        case (ProofCIntConst(_,_), ProofCIntConst(_,_)) => context
        case (ProofCSetLiteral(elems), ProofCSetLiteral(call_elems)) =>
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
      Context(
        spec.existensial_params.toList,
        (
          spec.c_params.map({ case (name, ty) => (name, CoqParamType(ty)) }) ++
            spec.formal_params ++
            spec.existensial_params
          ).toMap,
        Map(),
        Nil,
        Nil
      )

    def retrieve_typing_context: Context => Map[Ident, VSTProofType] = _.gamma

    def add_new_variables(new_params: Map[Ident, VSTProofType])(context: Context): Context = context match {
      case Context(post, old_params, ex_map, funs, ufs) => Context(post, old_params ++ new_params, ex_map, funs, ufs)
    }

    def pop_function(context: Context): (FunSpec, Context) = context match {
      case Context(post, old_params, ex_map, fun :: funs, ufs) => (fun, Context(post, old_params, ex_map, funs,ufs))
      case _ => fail_with("Function called without prior abduce call")
    }

    def push_function(fun_spec: FunSpec)(context: Context): Context = context match {
      case Context(post, old_params, ex_map, old_funs, ufs) => Context(post, old_params, ex_map, fun_spec :: old_funs, ufs)
    }

    def push_unfolding(context: Context)(unfolded_expr: Unfold, new_equalities: Map[String, ProofCExpr]): Context =
      context match {
        case Context(post, gamma, variable_map, functions, queued_unfolds) =>
          Context(post, gamma, variable_map ++ new_equalities, functions, unfolded_expr :: queued_unfolds)
      }

    def record_variable_assignment(name: String, expr: Expr)(context: Context): Context = {
      // when recording a mapping of a pointer, force any int constants to be pointers (suslik doesn't always place them in loc_consts)
      val translated = ProofSpecTranslation.translate_expression(context.gamma)(expr)
      val result = (context.gamma.get(name), translated) match {
          case (Some (CoqPtrType), ProofCIntConst(value, _)) => ProofCIntConst(value,true)
         case (_, translated) => translated
      }
      Context(
        context.post,
        context.gamma,
        (context.variable_map ++ Map(name -> result)),
        context.functions,
        context.queued_unfolds
      )
    }

    def record_variable_assignment_card(name: String, expr: ProofCExpr)(context:Context) =
      Context(
        context.post,
        context.gamma,
        (context.variable_map ++ Map(name -> expr)),
        context.functions,
        context.queued_unfolds
      )



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
        (fun_name, args.map(arg => variable_mapping.getOrElse(arg, arg)), existentials) })
      val new_variable_map = update_map(context.variable_map)
      val new_unfolds = context.queued_unfolds.map({
        case Unfold(predicate, cardinality, args, existentials) =>
          val new_cardinality = cardinality match {
            case ProofTerms.CardNull => ProofTerms.CardNull
            case ProofTerms.CardOf(args) =>  ProofTerms.CardOf(args.map({case (name) => variable_mapping.getOrElse(name,name)}))
          }
          val new_args = args.map({case (name,ty) => (variable_mapping.getOrElse(name,name), ty)})
          val new_existentials = existentials.map({case (name, ty) => (variable_mapping.getOrElse(name,name), ty)})
          Unfold(predicate, new_cardinality, new_args, new_existentials)
      })
      Context(post, new_params, new_variable_map, new_funs, new_unfolds)
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
    def handle_read_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.Read(subst, option) =>
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

            def is_variable_used_in_proof(variable: Ident)(node: ProofRule.Node): Boolean = {
              def map_varaible(map: Map[Var, Expr]): Ident =
                map.get(Var(variable)).flatMap({ case Var(name) => Some(name) case _ => None }).getOrElse(variable)

              node.rule match {
                case ProofRule.PickArg(_) =>
                  val picked_variables = subst.toList.flatMap({ case (Var(froe), Var(toe)) => Some(toe) case _ => None }).toSet
                  (picked_variables.contains(variable)) || is_variable_used_in_proof(variable)(node.next.head)
                case ProofRule.Pick(subst) =>
                  val picked_variables = subst.toList.flatMap({ case (Var(froe), Var(toe)) => Some(toe) case _ => None }).toSet
                  (picked_variables.contains(variable)) || is_variable_used_in_proof(variable)(node.next.head)
                case ProofRule.AbduceBranch(cond, bLabel) =>
                  val Seq(ifTrue, ifFalse) = node.next
                  is_variable_used_in_exp(variable)(cond) ||
                    is_variable_used_in_proof(variable)(ifTrue) ||
                    is_variable_used_in_proof(variable)(ifFalse)
                case ProofRule.Write(Statements.Store(Var(tov), offset, e)) =>
                  (tov == variable) || is_variable_used_in_exp(variable)(e) || is_variable_used_in_proof(variable)(node.next.head)
                case ProofRule.EmpRule => false
                case ProofRule.Open(pred, fresh_vars, sbst, selectors) =>
                  val cases = selectors.zip(node.next)
                  cases.exists({ case (expr, next) =>
                    is_variable_used_in_exp(variable)(expr) ||
                      is_variable_used_in_proof(variable)(next)
                  })
                case ProofRule.SubstL(map) => is_variable_used_in_proof(map_varaible(map))(node.next.head)
                case ProofRule.SubstR(map) => is_variable_used_in_proof(map_varaible(map))(node.next.head)
                case ProofRule.HeapUnifyPointer(map) => is_variable_used_in_proof(map_varaible(map))(node.next.head)
                case ProofRule.Read(map, Load(Var(toe), _, Var(frome), offset)) =>
                  (frome == variable) || ((toe != variable) && is_variable_used_in_proof(variable)(node.next.head))
                case ProofRule.Call(_, Call(_, args, _)) =>
                  args.exists(is_variable_used_in_exp(variable)) ||
                    is_variable_used_in_proof(variable)(node.next.head)
                case ProofRule.Free(Free(Var(v)), _) =>
                  (v == variable) || is_variable_used_in_proof(variable)(node.next.head)
                case ProofRule.Malloc(map, Malloc(Var(toe), tpe, sz)) =>
                  (toe != variable) && is_variable_used_in_proof(variable)(node.next.head)
                case _ => is_variable_used_in_proof(variable)(node.next.head)
              }
            }

            val new_context = record_variable_mapping(subst)(context)
            val rest = (retrieve_typing_context(context).get(old_var)) match {
              case Some(CoqPtrType) =>
                ProofSteps.ValidPointerOrNull(new_var, translate_proof_rules(node.next.head)(new_context))
              case _ => translate_proof_rules(node.next.head)(new_context)
            }
            if (is_variable_used_in_proof(new_var)(node.next.head)) {
              ProofSteps.Rename(old_var, new_var,
                ProofSteps.Forward(
                  rest
                )
              )
            } else {
              ProofSteps.Rename(old_var, new_var,
                rest
              )
            }
        }
    }

    /**
      * Translates a suslik Open Rule into the corresponding VST rules
      *
      * Does this by mapping each constructor of the opened predicate to a branch of the rule,
      * and then for each branch introducing the variables that it uses.
      */
    def handle_open_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.Open(SApp(predicate_name, args, _, Var(card_variable)), fresh_vars, sbst, selectors) =>
        val pred = pred_map(predicate_name)
        val cases = selectors.zip(node.next)
        ProofSteps.ForwardIfConstructor(
          card_variable,
          predicate_name,
          pred.clauses.zip(cases).map({
            case ((constructor, clause), (expr, next)) =>
              // each clause of the type introduces existentials
              val new_variables = pred.constructor_existentials(constructor).map({
                // rename existential variables if they have been assigned fresh variables
                case (variable, ty) => fresh_vars.get(Var(variable)).map({ case Var(new_name) => (new_name, ty) }).getOrElse((variable, ty))
              })
              val constructor_args = constructor.constructor_args.map(v => fresh_vars(Var(v)).name)
              val new_context = add_new_variables(
                new_variables.toMap ++
                constructor_args.map(v => (v, CoqCardType(pred.inductive_name))).toMap
              )(context)
              // val (args, constructor_args) = partition_cardinality_args(new_variables)()
              ((pred.constructor_name(constructor), constructor, constructor_args),
                ProofSpecTranslation.translate_expression(retrieve_typing_context(context).toMap)(expr),
                new_variables.map(_._1),
                translate_proof_rules(next)(new_context))
          }).toList
        )
    }

    def handle_pick_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.Pick(subst) =>
        val new_context = subst.map({case (Var(name), expr) => (name,expr) }).foldRight(context)({
          case ((name,expr), context) =>   record_variable_assignment(name,expr)(context)
        })
        translate_proof_rules(node.next.head)(new_context)
    }

    def handle_pick_card_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.PickCard(subst) =>

        /** Given an expression representing a pick of a cardinality variable
          * returns the corresponding cardinality constructor
          *
          * i.e
          *    _alpha_512 -> _alpha_514 + 1
          *
          *      produces
          *       (lseg_card_1 _alpha_514), [(_alpha_514, lseg_card)]
          *       (i.e, the picked cardinality is that alpha_512 maps to lseg_card_1 _alpha_514, where _alpha_514 is a new existential variable)
          */
        def cardinality_expr_mapping_to_cardinality_map(base_expr: String)(expr: Expressions.Expr) : (ProofCExpr, List[(Ident, VSTProofType)]) =
          expr match {
            case Var(name) =>
              context.gamma.get(name) match {
                case Some(ty) => (ProofCVar(name, ty), Nil)
                case None => (ProofCVar(name, context.gamma(base_expr)), List((name, context.gamma(base_expr))))
              }
            case rule@Expressions.BinaryExpr(Expressions.OpPlus, expr, Expressions.IntConst(_)) =>
              val (translated_expr, new_vars) = cardinality_expr_mapping_to_cardinality_map(base_expr)(expr)
              val pred_name = context.gamma(base_expr) match { case ProofTypes.CoqCardType(pred_type) => pred_type }
              val predicate = pred_map(pred_name)
              // NOTE: Assumes that all predicates have a 1-argument constructor
              (ProofCCardinalityConstructor(predicate.inductive_name, predicate.constructor_name(predicate.constructor_by_arg(1)), List(translated_expr)), new_vars)
          }

        val new_context = subst.map({case (Var(name), expr) => (name,expr) }).foldRight(context)({
          case ((name,expr), context) =>
            val (translated_expr, new_vars) = cardinality_expr_mapping_to_cardinality_map(name)(expr)
            record_variable_assignment_card(name, translated_expr)(
              add_new_variables(new_vars.toMap)(context)
            )
        })
        translate_proof_rules(node.next.head)(new_context)
    }

    def handle_pick_arg_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.PickArg(subst) =>
        val new_context = subst.map({case (Var(name), expr) => (name,expr) }).foldRight(context)({
          case ((name,expr), context) =>   record_variable_assignment(name,expr)(context)
        })
        translate_proof_rules(node.next.head)(new_context)
    }

    def handle_emp_rule(context: Context) = {
      def instantiate_existentials(existentials: List[(Ident, VSTProofType)])(then: ProofSteps) : ProofSteps =
        existentials.foldRight(then)(
          (variable, next) => ProofSteps.Exists(context.variable_map(variable._1), next)
        )
      def unfold_predicates(then: ProofSteps) : ProofSteps =
        context.queued_unfolds.foldRight(then)(
          {case (unfold, next) =>
            val predicate : VSTPredicate = unfold.VSTPredicate
            ProofSteps.Unfold (
              predicate,
              unfold.VSTPredicate.params.length,
              ProofCCardinalityConstructor(
                predicate.inductive_name,
                predicate.constructor_name(unfold.cardinality),
                unfold.cardinality.constructor_args.map(v => ProofCVar(v, CoqCardType(predicate.inductive_name)))),
              unfold.existentials.foldRight(next)
              ({case ((variable,ty), next) => ProofSteps.Exists(context.variable_map.getOrElse(variable, ProofCVar(variable,ty)) , next)})
            )}
        )

      ProofSteps.ForwardEntailer(
        instantiate_existentials(context.post)(
          context.post match { // If no existentials, only entailer will be at the end of the unfoldings
            case Nil =>
              context.queued_unfolds match {
                case Nil => ProofSteps.Qed
                case ::(_, _) => unfold_predicates(ProofSteps.Entailer (ProofSteps.Qed))
              }
            case ::(_, _) =>
              context.queued_unfolds match {
                case Nil => ProofSteps.Entailer (ProofSteps.Qed)
                case ::(_, _) => ProofSteps.Entailer (unfold_predicates(ProofSteps.Entailer (ProofSteps.Qed)))
              }
          }
        )
      )
    }

    def handle_pure_synthesis_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.PureSynthesis(is_final, subst) =>
        val new_context = subst.map({case (Var(name), expr) => (name,expr) }).foldRight(context)({
          case ((name,expr), context) =>   record_variable_assignment(name,expr)(context)
        })
        translate_proof_rules(node.next.head)(new_context)
    }

    def handle_heap_unify(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.HeapUnify(_) =>
//        val new_context = subst.map({case (Var(name), expr) => (name,expr) }).foldRight(context)({
//          case ((name,expr), context) =>   record_variable_assignment(name,expr)(context)
//        })
        translate_proof_rules(node.next.head)(context)
    }

    def handle_heap_unify_pointer(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.HeapUnifyPointer(subst) =>
        val new_context = subst.map({case (Var(name), expr) => (name,expr) }).foldRight(context)({
          case ((name,expr), context) =>   record_variable_assignment(name,expr)(context)
        })
        translate_proof_rules(node.next.head)(new_context)
    }

    def handle_substl_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.SubstL(map) =>
        map.toList.foldRight(translate_proof_rules(node.next.head)(context))({
          case ((Var(name), expr), next) =>
            AssertPropSubst(
              name,
              ProofSpecTranslation.translate_expression(retrieve_typing_context(context))(expr),
              next)
        })
    }

    def handle_substr_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.SubstR(map) =>
        def apply_subst(context: Context)(map: List[(Var, Expr)]): ProofSteps =
          map match {
            case Nil => translate_proof_rules(node.next.head)(context)
            case ::((Var(old_name), Var(new_name)), rest) =>
              val new_context = record_variable_mapping(Map(Var(old_name) -> Var(new_name)))(context)
              ProofSteps.Rename(old_name, new_name,
                apply_subst(new_context)(rest)
              )
            case ::((Var(name), expr), rest) =>
              val new_context = record_variable_assignment(name, expr)(context)
              apply_subst(new_context)(rest)
          }

        apply_subst(context)(map.toList)
    }

    def handle_abduce_call(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.AbduceCall(new_vars, f_pre, callePost, Call(Var(fun), _, _), freshSub, _, _, _) =>
        var typing_context = retrieve_typing_context(context)
        f_pre.vars.foreach({ case Var(name) =>
          if (!typing_context.contains(name)) {
                      typing_context = typing_context + (name -> CoqPtrType)
                  }})
        val call_precond = ProofSpecTranslation.translate_assertion(typing_context)(f_pre)
        val call_args = unify_call_params(call_precond).map({ case (name, _) => name })
        val existentials = spec.existensial_params.toList.map({case (name,ty) => (freshSub(Var(name)).name, ty)})
        var new_context = push_function((fun, call_args, existentials))(context)
        translate_proof_rules(node.next.head)(new_context)
    }

    def handle_nilnotnval_rule(node: ProofRule.Node, context: Context) = node.rule match {
      case ProofRule.NilNotLval(vars) =>
        vars.foldRight(translate_proof_rules(node.next.head)(context))({
          case (_@Var(name), rest) => ProofSteps.ValidPointer(
            name, rest
          )
        })
    }

    def handle_abduce_branch_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.AbduceBranch(cond, bLabel) =>
        val Seq(ifTrue, ifFalse) = node.next
        ProofSteps.ForwardIf(List(
          translate_proof_rules(ifTrue)(context),
          translate_proof_rules(ifFalse)(context)
        ))
    }

    def handle_call_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.Call(_, call) =>
        val ((fun, args, existentials), new_context) = pop_function(context)
        ProofSteps.ForwardCall(args,
          existentials match {
            case Nil => translate_proof_rules(node.next.head)(new_context)
            case _ =>
              ProofSteps.IntrosTuple(existentials, translate_proof_rules(node.next.head)(new_context))
          })
    }

    def handle_write_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.Write(stmt) => ProofSteps.Forward(translate_proof_rules(node.next.head)(context))
    }

    def handle_free_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.Free(Free(Var(name)), size) => ProofSteps.Free(name, size, translate_proof_rules(node.next.head)(context))
    }

    def handle_close_rule(node: ProofRule.Node, context: Context): ProofSteps = node.rule match {
      case ProofRule.Close(app, o_selector, asn, fresh_exist) =>

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
          name => (name, CoqCardType(predicate.inductive_name))
        )
        val unfolding = Unfold(predicate, cardinality, args,  clause_existentials)
        val new_context = push_unfolding(context)(unfolding, new_equalities)
        val new_context_2 = record_variable_mapping(fresh_exist)(new_context)

        translate_proof_rules(node.next.head)(new_context_2)
    }

    def handle_malloc_rule(node: ProofRule.Node, context: Context) = node.rule match {
      case ProofRule.Malloc(map, Malloc(Var(to_var), _, sz)) =>
        val new_context =
          map.foldRight(
            add_new_variables(map.map({case (Var(original), Var(name)) => (name, CoqPtrType)}))(context)
          )({case ((Var(old_name), new_expr), context) => record_variable_assignment(old_name,new_expr)(context)})
        ProofSteps.Malloc(sz,
          ProofSteps.Intros(
            List((to_var, CoqPtrType)),
            translate_proof_rules(node.next.head)(new_context)
          ))
    }

    def translate_proof_rules(node: ProofRule.Node)(context: Context): ProofSteps = {
      node.rule match {
        //          Branching rules
        case ProofRule.Open(SApp(_, _, _, Var(_)), _, _, _) => handle_open_rule(node, context)
        case ProofRule.AbduceBranch(cond, bLabel) => handle_abduce_branch_rule(node, context)

        //          Read and write Operations
        case ProofRule.Write(_) => handle_write_rule(node, context)
        case ProofRule.Read(subst, option) => handle_read_rule(node, context)

        //          Memory management rules
        case ProofRule.Free(Free(Var(_)), _) => handle_free_rule(node, context)
        case ProofRule.Malloc(map, Malloc(Var(to_var), _, sz)) => handle_malloc_rule(node, context)

        //          Abduce call & Existentials
        case ProofRule.AbduceCall(_, _, _, Call(Var(_), _, _), _, _, _, _) => handle_abduce_call(node, context)
        case ProofRule.Pick(_) => handle_pick_rule(node, context)
        case ProofRule.PureSynthesis(_, _) => handle_pure_synthesis_rule(node, context)
        case ProofRule.PickCard(_) => handle_pick_card_rule(node, context)
        case ProofRule.PickArg(_) => handle_pick_arg_rule(node, context)
        case ProofRule.Call(_, _) => handle_call_rule(node, context)
        case ProofRule.Close(_, _, _, _) => handle_close_rule(node, context)
        case ProofRule.HeapUnify(_) => handle_heap_unify(node, context)
        case ProofRule.HeapUnifyPointer(_) => handle_heap_unify_pointer(node, context)


        //          Completion rule
        case ProofRule.EmpRule => handle_emp_rule(context)

        //          Context changing rules
        case ProofRule.NilNotLval(_) => handle_nilnotnval_rule(node, context)
        case ProofRule.SubstL(_) => handle_substl_rule(node, context)
        case ProofRule.SubstR(_) => handle_substr_rule(node, context)

        //          Ignored rules
        case ProofRule.WeakenPre(unused) => translate_proof_rules(node.next.head)(context)
        case ProofRule.CheckPost(pre_phi, post_phi) => translate_proof_rules(node.next.head)(context)

        case ProofRule.FrameUnfold(h_pre, h_post) => translate_proof_rules(node.next.head)(context)


        case ProofRule.StarPartial(new_pre_phi, new_post_phi) => translate_proof_rules(node.next.head)(context)
        case ProofRule.Branch(cond) => translate_proof_rules(node.next.head)(context)
        case ProofRule.Init(goal) => translate_proof_rules(node.next.head)(context)
      }
    }

    val simplified = ProofRule.of_certtree(root)
    println(s"Suslik Proof:\n ${simplified.pp}")

    val vst_proof: ProofSteps = translate_proof_rules(simplified)(initial_context)

    Proof(name, predicates, spec, vst_proof, contains_free(simplified), contains_malloc(simplified))
  }

  def contains_free(proof: ProofRule.Node): Boolean = proof.rule match {
    case _:ProofRule.Free => true
    case ProofRule.EmpRule | ProofRule.Inconsistency => false
    case _:ProofRule.Branch => contains_free(proof.next.head)
    case _ => proof.next.exists(contains_free)
  }

  def contains_malloc(proof: ProofRule.Node): Boolean = proof.rule match {
    case _:ProofRule.Malloc => true
    case ProofRule.EmpRule | ProofRule.Inconsistency => false
    case _:ProofRule.Branch => contains_malloc(proof.next.head)
    case _ => proof.next.exists(contains_malloc)
  }

}
