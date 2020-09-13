package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CDataAt, CSApp, VSTHeaplet}
import org.tygus.suslik.certification.targets.vst.logic.ProofRule.EmpRule
import org.tygus.suslik.certification.targets.vst.logic.ProofSteps.AssertPropSubst
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.Expressions.{ProofCBinaryExpr, ProofCBoolConst, ProofCExpr, ProofCIfThenElse, ProofCIntConst, ProofCSetLiteral, ProofCUnaryExpr, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{VSTPredicate, VSTPredicateClause}
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.{CoqParamType, CoqPtrType, VSTProofType}
import org.tygus.suslik.certification.targets.vst.{Debug, State}
import org.tygus.suslik.certification.targets.vst.logic.{Formulae, Proof, ProofRule, ProofSteps, ProofTerms}
import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Var}
import org.tygus.suslik.language.{Expressions, Ident, PrettyPrinting, Statements}
import org.tygus.suslik.language.Statements.{Call, Free, Load, Malloc, Skip, Store}
import org.tygus.suslik.logic.Preprocessor.{findMatchingHeaplets, sameLhs}
import org.tygus.suslik.logic.Specifications.SuspendedCallGoal
import org.tygus.suslik.logic.{Block, Heaplet, PFormula, PointsTo, SApp, SFormula}
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

  /** converts a single proof node into a compressed rule */
  def proof_rule_of_proof_node(node: CertTree.Node): ProofRule = {
    def fail_with_bad_proof_structure(): Nothing = {
      throw ProofRuleTranslationException(s"continuation for ${node.rule} is not what was expected: ${node.kont.toString}")
    }

    def fail_with_bad_children(ls: List[CertTree.Node], count: Int): Nothing = {
      throw ProofRuleTranslationException(s"unexpected number of children for proof rule ${node.rule} - ${ls.length} != ${count}")
    }

    node.rule match {
      case LogicalRules.NilNotLval => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(_)) => {
          // find all pointers that are not yet known to be non-null
          def find_pointers(p: PFormula, s: SFormula): Set[Expr] = {
            // All pointers
            val allPointers = (for (PointsTo(l, _, _) <- s.chunks) yield l).toSet
            allPointers.filter(
              x => !p.conjuncts.contains(x |/=| NilPtr) && !p.conjuncts.contains(NilPtr |/=| x)
            )
          }

          val pre_pointers = find_pointers(node.goal.pre.phi, node.goal.pre.sigma).toList

          node.children match {
            case ::(head, Nil) => ProofRule.NilNotLval(pre_pointers, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        }
        case v => fail_with_bad_proof_structure()
      }
      case FailRules.CheckPost => node.kont match {
        case IdProducer => node.children match {
          case ::(head, Nil) => ProofRule.CheckPost(proof_rule_of_proof_node(head))
          case ls => fail_with_bad_children(ls, 1)
        }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.Pick => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Pick(map, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case FailRules.AbduceBranch => node.kont match {
        case GuardedProducer(cond, _) =>
          node.children match {
            case ::(if_true, ::(if_false, Nil)) => ProofRule.AbduceBranch(cond, proof_rule_of_proof_node(if_true), proof_rule_of_proof_node(if_false))
            case ls => fail_with_bad_children(ls, 2)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.WriteRule => node.kont match {
        case ChainedProducer(ChainedProducer(PrependProducer(stmt@Store(_, _, _)), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Write(stmt, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.WeakenPre => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val unused = goal.pre.phi.indepedentOf(goal.pre.sigma.vars ++ goal.post.vars)
          node.children match {
            case ::(head, Nil) => ProofRule.WeakenPre(unused, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.EmpRule => node.kont match {
        case ConstProducer(Skip) =>
          node.children match {
            case Nil => ProofRule.EmpRule
            case ls => fail_with_bad_children(ls, 0)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case DelegatePureSynthesis.PureSynthesisFinal => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(assignments), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofRule.PureSynthesis(true, assignments, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Open => node.kont match {
        case ChainedProducer(ChainedProducer(BranchProducer(Some((heaplet, fresh_vars)), selectors), HandleGuard(_)), ExtractHelper(_)) =>
          ProofRule.Open(heaplet, fresh_vars, selectors.zip(node.children).map({ case (expr, node) => (expr, proof_rule_of_proof_node(node)) }).toList)
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.SubstLeft => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.SubstL(map, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.SubstRight => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.SubstR(map, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.ReadRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Load(_, _, _, _))), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Read(map, stmt, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.AbduceCall => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>

              // find out which new variables were added to the context
              val new_vars =
                head.goal.gamma.filterKeys(key => !(node.goal.gamma.contains(key)))
              var f_pre = head.goal.post

              var SuspendedCallGoal(_, _, callePost, call, freshSub, _) = head.goal.callGoal.get
              ProofRule.AbduceCall(new_vars, f_pre, callePost, call, freshSub, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPure => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.HeapUnify(proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyUnfolding => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.HeapUnify(proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyBlock => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.HeapUnify(proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPointer => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post
              val prePtss = pre.sigma.ptss
              val postPtss = post.sigma.ptss

              def lcpLen(s1: String, s2: String): Int = s1.zip(s2).takeWhile(Function.tupled(_ == _)).length

              val alternatives = for {
                PointsTo(y, oy, _) <- postPtss
                if y.vars.exists(goal.isExistential)
                t@PointsTo(x, ox, _) <- prePtss
                if ox == oy
                if !postPtss.exists(sameLhs(t))
              } yield (y -> x)
              alternatives.minBy { case (e1, e2) => -lcpLen(e1.pp, e2.pp) } match {
                case (y: Var, x) => ProofRule.HeapUnifyPointer(Map(y -> x), proof_rule_of_proof_node(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameUnfolding => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameUnfolding.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, proof_rule_of_proof_node(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameUnfoldingFinal => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameUnfoldingFinal.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, proof_rule_of_proof_node(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameBlock => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameBlock.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, proof_rule_of_proof_node(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameFlat => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameFlat.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, proof_rule_of_proof_node(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.CallRule => node.kont match {
        case ChainedProducer(ChainedProducer(PrependProducer(call: Call), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Call(call, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.FreeRule => node.kont match {
        case ChainedProducer(ChainedProducer(PrependProducer(stmt@Free(Var(name))), HandleGuard(_)), ExtractHelper(_)) =>
          val size : Int = node.goal.pre.sigma.blocks.find({ case Block(Var(ploc), sz) => ploc == name }).map({ case Block(_, sz) => sz }) match {
            case Some(value) => value
            case None => 1
          }
          node.children match {
            case ::(head, Nil) => ProofRule.Free(stmt, size, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.AllocRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Malloc(_, _, _))), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofRule.
                Malloc(map, stmt, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Close => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(UnfoldProducer(app, selector, pred_subst, fresh_exist, subst_args), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofRule.Close(app, selector, pred_subst, fresh_exist, subst_args, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case LogicalRules.StarPartial => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val new_pre_phi = extendPure(goal.pre.phi, goal.pre.sigma)
          val new_post_phi = extendPure(goal.pre.phi && goal.post.phi, goal.post.sigma)

          node.children match {
            case ::(head, Nil) =>
              ProofRule.StarPartial(new_pre_phi, new_post_phi, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }

      case UnificationRules.PickCard => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.PickCard(proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case UnificationRules.PickArg => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.PickArg(map, proof_rule_of_proof_node(head))
            case ls => fail_with_bad_children(ls, 1)
          }
      }

    }

  }


  def generate_args(new_variables: List[(String, VSTProofType)]) (card_args: List[String]) = {
    var seen_variables_set : Set[String] = Set()
    var contructor_map : Map[Ident, Ident] = Map()
    val args = new_variables.flatMap({
      case (variable_name, ty) =>
      if (!seen_variables_set.contains(variable_name)){
        seen_variables_set = seen_variables_set + variable_name
        (card_args.find(name => variable_name.startsWith(name))) match {
          case Some(name) =>
            contructor_map = contructor_map + (name -> variable_name)
            None
          case None =>
            Some(variable_name)
        }
      }   else {
        None
      }
    })
    (args, card_args.map(arg => contructor_map(arg)))
  }

  def translate_proof(predicates: List[VSTPredicate], spec: ProofTerms.FormalSpecification, root: CertTree.Node, pre_cond: ProofTerms.FormalCondition): Proof = {
    val pred_map = predicates.map(v => (v.name, v)).toMap

    type FunSpec = (Ident, List[Ident])
    type Context = (Map[Ident, VSTProofType], List[(Ident, List[Ident])])


    def unify_expr (context: Map[Ident,Ident]) (pure:ProofCExpr) (call: ProofCExpr) : Map[Ident,Ident] =
      (pure, call) match {
        case (ProofCVar(name, _), ProofCVar(call_name, _)) => context + (name -> call_name)
        case (ProofCBoolConst(_), ProofCBoolConst(_)) => context
        case (ProofCIntConst(_), ProofCIntConst(_)) => context
        case (ProofCSetLiteral(elems), ProofCSetLiteral(call_elems)) =>
          elems.zip(call_elems).foldLeft(context)({case (context, (expr, call_expr)) => unify_expr(context)(expr)(call_expr)})
        case (ProofCIfThenElse(cond, left, right), ProofCIfThenElse(call_cond, call_left, call_right)) =>
          var new_context = unify_expr(context)(cond)(call_cond)
          new_context = unify_expr(new_context)(left)(call_left)
          unify_expr(new_context)(right)(call_right)
        case (ProofCBinaryExpr(_, left, right),ProofCBinaryExpr(_, call_left, call_right)) =>
          val new_context = unify_expr(context)(left)(call_left)
          unify_expr(new_context)(right)(call_right)
        case (ProofCUnaryExpr(_, e),ProofCUnaryExpr(_, call_e)) =>
          unify_expr(context)(e)(call_e)
      }

    def unify_call_params (call_pre: ProofTerms.FormalCondition) : List[(Ident, VSTProofType)] = {
      (pre_cond,call_pre) match {
        case (ProofTerms.FormalCondition(pure, spatial),ProofTerms.FormalCondition(call_pure, call_spatial)) =>
          def unify_pure(context: Map[Ident, Ident])(pure: ProofTerms.PureFormula) (call: ProofTerms.PureFormula) : Map[Ident,Ident] = {
            (pure, call) match {
              case (ProofTerms.IsValidPointerOrNull(CVar(name)),ProofTerms.IsValidPointerOrNull(CVar(name1))) =>
                context + (name -> name1)
              case (ProofTerms.IsValidInt(CVar(name)), ProofTerms.IsValidInt(CVar(name1))) =>
                context + (name -> name1)
              case (ProofTerms.IsTrueProp(expr), ProofTerms.IsTrueProp(expr1)) =>
                unify_expr(context)(expr)(expr1)
              case (ProofTerms.IsTrue(expr), ProofTerms.IsTrue(expr1)) =>
                unify_expr(context)(expr)(expr1)
            }
          }
          def unify_spatial(context: Map[Ident, Ident])(pure: VSTHeaplet)(call: VSTHeaplet) : Map[Ident,Ident] = {
            (pure,call) match {
              case (CDataAt(loc, elem_ty, count, elem), CDataAt(call_loc, call_elem_ty, call_count, call_elem)) =>
                unify_expr(unify_expr(context)(loc)(call_loc))(elem)(call_elem)
              case (CSApp(pred, args, card), CSApp(call_pred, call_args, call_card)) =>
                assert(pred == call_pred)
                unify_expr(args.zip(call_args).foldRight(context)({case ((exp, call_exp), context) =>
                  unify_expr(context)(exp)(call_exp)
                }))(card)(call_card)
            }
          }
          var context =  pure.zip(call_pure).foldLeft(Map[Ident,Ident]())({case (context, (pure, call_pure)) => unify_pure(context)(pure)(call_pure)})
          context =  spatial.zip(call_spatial).foldLeft(context)({case (context, (pure, call_pure)) => unify_spatial(context)(pure)(call_pure)})
          spec.params.map({case (name, ty) => (context(name), ty)})
      }
    }

    def initial_context: Context =
      ((spec.c_params.map({ case (name, ty) => (name, CoqParamType(ty)) }) ++
        spec.formal_params).toMap, Nil)

    def retrieve_typing_context: Context => Map[Ident, VSTProofType] = {
      case (gamma, _) => gamma
    }

    def add_new_variables(new_params: Map[Ident, VSTProofType])(context: Context): Context = context match {
      case (old_params, funs) => (old_params ++ new_params, funs)
    }

    def pop_function(context: Context): (FunSpec, Context) = context match {
      case (old_params, fun :: funs) => (fun, (old_params, funs))
    }

    def push_function(fun_spec: FunSpec)(context: Context): Context = context match {
      case (old_params, old_funs) => (old_params, fun_spec :: old_funs)
    }

    def record_variable_mapping(mapping: Map[Var, Expr])(context: Context): Context = {
      val variable_mapping = mapping.flatMap({ case (Var(old_name), Var(new_name)) => Some((old_name, new_name)) case _ => None })
      context match {
        case (old_params, funs) =>
          val new_params = old_params.map({ case (name, ty) => (variable_mapping.getOrElse(name, name), ty) })
          val new_funs = funs.map({ case (fun_name, args) => (fun_name, args.map(arg => variable_mapping.getOrElse(arg, arg))) })
          (new_params, new_funs)
      }
    }


    def translate_proof_rules(rule: ProofRule)(context: Context): ProofSteps = {
      rule match {
        case ProofRule.Open(SApp(predicate_name, args, _, Var(card_variable)), fresh_vars, cases) =>
          val arg_set = args.toSet
          val pred = pred_map(predicate_name)
          ProofSteps.ForwardIfConstructor(
            card_variable,
            predicate_name,
            pred.clauses.zip(cases).map({
              case ((constructor, clause), (expr, rule)) =>
                val new_variables = pred.constructor_existentials(constructor).map({
                  case (variable, ty) =>
                  fresh_vars.get(Var(variable)).map({case Var(new_name) => (new_name, ty)}).getOrElse((variable,ty))
                })
                val variable_map = new_variables.toMap
                val new_context = add_new_variables(variable_map)(context)

                val (args, constructor_args) = generate_args(new_variables)(constructor.constructor_args)

                ((pred.constructor_name(constructor), constructor, constructor_args),
                  ProofSpecTranslation.translate_expression(retrieve_typing_context(context).toMap)(expr),
                  args,
                  translate_proof_rules(rule)(new_context))
            }).toList
          )
        case ProofRule.NilNotLval(vars, next) => ???
        case ProofRule.CheckPost(next) => ???
        case ProofRule.Pick(subst, next) => ???
        case ProofRule.AbduceBranch(cond, ifTrue, ifFalse) => ???
        case ProofRule.Write(stmt, next) => ???
        case ProofRule.WeakenPre(unused, next) => translate_proof_rules(next)(context)
        case ProofRule.EmpRule => ProofSteps.Forward(ProofSteps.Qed)
        case ProofRule.PureSynthesis(is_final, assignments, next) => ???
        case ProofRule.SubstL(map, next) =>
          map.toList.foldRight(translate_proof_rules(next)(context))({
            case ((Var(name), expr), next) =>
              AssertPropSubst(
                name,
                ProofSpecTranslation.translate_expression(retrieve_typing_context(context))(expr),
                next)
          })
        case ProofRule.SubstR(map, next) =>
          map.toList match {
            case ::((Var(old_name), Var(new_name)), _) =>
              val new_context = record_variable_mapping(map)(context)
              ProofSteps.Rename(old_name, new_name,
              translate_proof_rules(next)(new_context)
              )
          }
        case ProofRule.Read(subst, operation, next) =>
          subst.toList match {
            case ::((Var(old_var), Var(new_var)), tl) =>
              def is_variable_used_in_exp(variable: Ident)(expr: Expr): Boolean = expr match {
                case Var(name) => (name == variable)
                case const: Expressions.Const => false
                case Expressions.BinaryExpr(op, left, right) => is_variable_used_in_exp(variable)(left) || is_variable_used_in_exp(variable)(right)
                case Expressions.OverloadedBinaryExpr(overloaded_op, left, right) =>
                  is_variable_used_in_exp(variable)(left) || is_variable_used_in_exp(variable)(right)
                case Expressions.UnaryExpr(op, arg) => is_variable_used_in_exp(variable)(arg)
                case Expressions.SetLiteral(elems) => elems.exists(is_variable_used_in_exp(variable))
                case Expressions.IfThenElse(cond, left, right) =>
                  is_variable_used_in_exp(variable)(cond) || is_variable_used_in_exp(variable)(left) || is_variable_used_in_exp(variable)(right)
              }
              def is_variable_used_in_proof(variable: Ident)(rule: ProofRule): Boolean = {
                def map_varaible(map: Map[Var, Expr]): Ident =
                  map.get(Var(variable)).flatMap({ case Var(name) => Some(name) case _ => None }).getOrElse(variable)

                rule match {
                  case ProofRule.NilNotLval(vars, next) => is_variable_used_in_proof(variable)(next)
                  case ProofRule.CheckPost(next) => is_variable_used_in_proof(variable)(next)
                  case ProofRule.PickCard(next) => is_variable_used_in_proof(variable)(next)
                  case ProofRule.PickArg(subst, next) =>
                    val picked_variables = subst.toList.flatMap({ case (Var(froe), Var(toe)) => Some(toe) case _ => None }).toSet
                    (picked_variables.contains(variable)) || is_variable_used_in_proof(variable)(next)
                  case ProofRule.Pick(subst, next) =>
                    val picked_variables = subst.toList.flatMap({ case (Var(froe), Var(toe)) => Some(toe) case _ => None }).toSet
                    (picked_variables.contains(variable)) || is_variable_used_in_proof(variable)(next)
                  case ProofRule.AbduceBranch(cond, ifTrue, ifFalse) =>
                    is_variable_used_in_exp(variable)(cond) ||
                      is_variable_used_in_proof(variable)(ifTrue) ||
                      is_variable_used_in_proof(variable)(ifFalse)
                  case ProofRule.Write(Statements.Store(Var(tov), offset, e), next) =>
                    (tov == variable) || is_variable_used_in_exp(variable)(e) || is_variable_used_in_proof(variable)(next)
                  case ProofRule.WeakenPre(unused, next) => is_variable_used_in_proof(variable)(next)
                  case ProofRule.EmpRule => false
                  case ProofRule.PureSynthesis(is_final, assignments, next) =>
                    is_variable_used_in_proof(variable)(next)
                  case ProofRule.Open(pred, heaplet, cases) =>
                    cases.exists({ case (expr, rule) =>
                      is_variable_used_in_exp(variable)(expr) ||
                        is_variable_used_in_proof(variable)(rule)
                    })
                  case ProofRule.SubstL(map, next) => is_variable_used_in_proof(map_varaible(map))(next)
                  case ProofRule.SubstR(map, next) => is_variable_used_in_proof(map_varaible(map))(next)
                  case ProofRule.AbduceCall(new_vars, f_pre, callePost, call, freshSub, next) =>
                    is_variable_used_in_proof(variable)(next)
                  case ProofRule.HeapUnify(next) => is_variable_used_in_proof(variable)(next)
                  case ProofRule.HeapUnifyPointer(map, next) => is_variable_used_in_proof(map_varaible(map))(next)
                  case ProofRule.FrameUnfold(h_pre, h_post, next) => is_variable_used_in_proof(variable)(next)
                  case ProofRule.Close(app, selector, pred_subst, fresh_exist, subst_args, next) =>
                    is_variable_used_in_proof(variable)(next)
                  case ProofRule.StarPartial(new_pre_phi, new_post_phi, next) =>
                    is_variable_used_in_proof(variable)(next)
                  case ProofRule.Read(map, Load(Var(toe), _, Var(frome), offset), next) =>
                    (frome == variable) || ((toe != variable) && is_variable_used_in_proof(variable)(next))
                  case ProofRule.Call(Call(_, args, _), next) =>
                    args.exists(is_variable_used_in_exp(variable)) ||
                      is_variable_used_in_proof(variable)(next)
                  case ProofRule.Free(Free(Var(v)), _, next) =>
                    (v == variable) || is_variable_used_in_proof(variable)(next)
                  case ProofRule.Malloc(map, Malloc(Var(toe), tpe, sz), next) =>
                    (toe != variable) && is_variable_used_in_proof(variable)(next)
                }
              }
              val new_context = record_variable_mapping(subst)(context)
              val rest = (retrieve_typing_context(context).get(old_var)) match {
                  case Some(CoqPtrType) =>
                    ProofSteps.ValidPointerOrNull(new_var, translate_proof_rules(next)(new_context))
                  case _ => translate_proof_rules(next)(new_context)
                }

              if (is_variable_used_in_proof(new_var)(next)) {
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
        case ProofRule.AbduceCall(new_vars, f_pre, callePost, Call(Var(fun), _, _), freshSub, next) =>
          var typing_context = retrieve_typing_context(context)
          f_pre.vars.foreach({case Var(name) => if (!typing_context.contains(name)) {
            typing_context = typing_context + (name -> CoqPtrType)
          } })
          val call_precond = ProofSpecTranslation.translate_assertion(typing_context)(f_pre)
          val call_args = unify_call_params(call_precond).map({case (name, _) => name})
          var new_context = push_function((fun, call_args))(context)
          translate_proof_rules(next)(new_context)
        case ProofRule.HeapUnify(next) => translate_proof_rules(next)(context)
        case ProofRule.HeapUnifyPointer(map, next) => translate_proof_rules(next)(context)
        case ProofRule.FrameUnfold(h_pre, h_post, next) => translate_proof_rules(next)(context)
        case ProofRule.Call(call, next) =>
          val ((fun, args),new_context) = pop_function(context)
          ProofSteps.ForwardCall(args, translate_proof_rules(next)(new_context))
        case ProofRule.Free(Free(Var(name)), size, next) =>
          ProofSteps.Free(name, size, translate_proof_rules(next)(context))
        case ProofRule.Malloc(map, stmt, next) => ???
        case ProofRule.Close(app, selector, pred_subst, fresh_exist, subst_args, next) => ???
        case ProofRule.StarPartial(new_pre_phi, new_post_phi, next) => ???
        case ProofRule.PickCard(next) => ???
        case ProofRule.PickArg(map, next) => ???
      }
    }

    val simplified = proof_rule_of_proof_node(root)
    println(s"Converted proof:\n ${simplified.pp}")

    val vst_proof: ProofSteps = translate_proof_rules(simplified)(initial_context)

    println("Converted proof:")
    println(vst_proof.pp)

    //Debug.visualize_ctree(root)
    //Debug.visualize_proof_tree(root.kont)

    ???
  }

}
