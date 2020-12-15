package org.tygus.suslik.certification.targets.vst.translation

import java.io

import org.tygus.suslik.certification.targets.htt.language.Expressions.CPointsTo
import org.tygus.suslik.certification.targets.vst.clang.{CTypes, PrettyPrinting}
import org.tygus.suslik.certification.targets.vst.clang.CTypes.{CIntType, CVoidPtrType, VSTCType}
import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CDataAt, CSApp, VSTHeaplet}
import org.tygus.suslik.certification.targets.vst.logic.{ProofTerms, ProofTypes}
import ProofTerms.Expressions.{ProofCBinOp, ProofCBinaryExpr, ProofCBoolConst, ProofCExpr, ProofCIfThenElse, ProofCIntConst, ProofCOpAnd, ProofCOpBoolEq, ProofCOpDiff, ProofCOpImplication, ProofCOpIn, ProofCOpIntEq, ProofCOpIntersect, ProofCOpLeq, ProofCOpLt, ProofCOpMinus, ProofCOpMultiply, ProofCOpNot, ProofCOpOr, ProofCOpPlus, ProofCOpPtrEq, ProofCOpSetEq, ProofCOpSubset, ProofCOpUnaryMinus, ProofCOpUnion, ProofCSetLiteral, ProofCUnOp, ProofCUnaryExpr, ProofCVar}
import ProofTerms.{CardConstructor, CardNull, CardOf, FormalCondition, FormalSpecification, IsTrueProp, IsValidInt, IsValidPointerOrNull, VSTPredicate, VSTPredicateClause}
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.{CoqCardType, CoqIntType, CoqListType, CoqParamType, CoqPtrType, VSTProofType}
import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.{BoolType, CardType, Expressions, Ident, IntSetType, IntType, LocType, SSLType}
import org.tygus.suslik.logic.{Block, Environment, FunSpec, Gamma, Heaplet, InductiveClause, InductivePredicate, PointsTo, PredicateEnv, SApp}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}

import scala.collection.immutable

/** translates suslik proof terms to VST compatible proof terms  */
object ProofSpecTranslation {

  /** translate a suslik type into a VST proof type */
  def translate_type(lType: SSLType): VSTProofType =
    lType match {
      case IntType => CoqIntType
      case LocType => CoqPtrType
      case CardType => CoqCardType("") // TODO: add a safe version of this (only used when initializing base context)

      // TODO: WARNING: Suslik has a loose model of memory that allows elements of different types
      // to be allocated in the same block - i.e x :-> [loc; int] - this is technically possible
      // but doesn't mesh well with C in which an allocated array must have all elements of the same type
      // otherwise a separate struct definition would be needed
      case IntSetType => CoqListType(CoqPtrType, None)
    }


  /** translate a suslik expression into a VST proof expression (note: this is not the same as a VST C expression, so can support terms like list comparisons etc.) */
  def translate_expression(context: Map[Ident, VSTProofType])(expr: Expressions.Expr): ProofTerms.Expressions.ProofCExpr = {
    def type_expr(left_1: ProofCExpr): VSTProofType =
      left_1 match {
        case ProofCVar(name, typ) => typ
        case ProofCIntConst(value) => CoqIntType
        case ProofCSetLiteral(elems) => CoqListType(CoqPtrType, Some(elems.length))
        case ProofCIfThenElse(cond, left, right) => type_expr(left)
        case ProofCBinaryExpr(op, left, right) =>
          op match {
            case ProofCOpPlus => CoqIntType
            case ProofCOpMinus => CoqIntType
            case ProofCOpMultiply => CoqIntType
            case ProofCOpUnion => CoqListType(CoqPtrType, None)
          }
        case ProofCUnaryExpr(op, e) => op match {
          case ProofCOpUnaryMinus => CoqIntType
        }
      }

    def translate_binop(op: Expressions.BinOp)(ty: VSTProofType): ProofCBinOp = {
      op match {
        case op: Expressions.RelOp => (op, ty) match {
          case (Expressions.OpEq, CoqIntType) => ProofCOpIntEq
          case (Expressions.OpEq, CoqParamType(CIntType)) => ProofCOpIntEq
          case (Expressions.OpEq, CoqPtrType) => ProofCOpPtrEq
          case (Expressions.OpEq, CoqParamType(CVoidPtrType)) => ProofCOpPtrEq
          case (Expressions.OpEq, _) => ProofCOpIntEq
          case (Expressions.OpBoolEq, _) => ProofCOpBoolEq
          case (Expressions.OpLeq, _) => ProofCOpLeq
          case (Expressions.OpLt, _) => ProofCOpLt
          case (Expressions.OpIn, _) => ProofCOpIn
          case (Expressions.OpSetEq,_) => ProofCOpSetEq
          case (Expressions.OpSubset, _) => ProofCOpSubset
        }
        case op: Expressions.LogicOp => op match {
          case Expressions.OpAnd => ProofCOpAnd
          case Expressions.OpOr => ProofCOpOr
        }
        case Expressions.OpImplication => ProofCOpImplication
        case Expressions.OpPlus => ProofCOpPlus
        case Expressions.OpMinus => ProofCOpMinus
        case Expressions.OpMultiply => ProofCOpMultiply
        case Expressions.OpUnion => ProofCOpUnion
        case Expressions.OpDiff => ProofCOpDiff
        case Expressions.OpIntersect => ProofCOpIntersect
      }
    }

    expr match {
      case const: Expressions.Const => const match {
        case Expressions.IntConst(value) => ProofCIntConst(value)
        case Expressions.LocConst(value) => ProofCIntConst(value) // TODO: handle ptr type
        case Expressions.BoolConst(value) => ProofCBoolConst(value)
      }
      case Var(name) => ProofCVar(name, context(name))
      case Expressions.SetLiteral(elems) => {
        ProofCSetLiteral(elems.map(translate_expression(context)))
      }
      case Expressions.UnaryExpr(op, arg) =>
        val top: ProofCUnOp = op match {
          case Expressions.OpNot => ProofCOpNot
          case Expressions.OpUnaryMinus => ProofCOpUnaryMinus
        }
        ProofCUnaryExpr(top, translate_expression(context)(arg))
      case Expressions.BinaryExpr(op, left, right) =>
        val left_expr = translate_expression(context)(left)
        val type_of_expr = type_expr(left_expr)
        val top: ProofCBinOp = translate_binop(op)(type_of_expr)
        ProofCBinaryExpr(top, left_expr, translate_expression(context)(right))
      case Expressions.IfThenElse(cond, left, right) =>
        ProofCIfThenElse(
          translate_expression(context)(cond),
          translate_expression(context)(left),
          translate_expression(context)(right)
        )
      case Expressions.OverloadedBinaryExpr(overloaded_op, left, right) =>
        val left_1 = translate_expression(context)(left)
        val right_1 = translate_expression(context)(right)
        overloaded_op match {
          case op: Expressions.BinOp =>
            val type_of_expr = type_expr(left_1)
            ProofCBinaryExpr(translate_binop(op)(type_of_expr), left_1, right_1)
          case Expressions.OpOverloadedEq =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpIntEq, left_1, right_1)
              case CoqListType(_, _) =>
                ProofCBinaryExpr(ProofCOpSetEq, left_1, right_1)
              case ProofTypes.CoqPtrType =>
                ProofCBinaryExpr(ProofCOpPtrEq, left_1, right_1)
            }
          case Expressions.OpNotEqual =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqIntType =>
                ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpIntEq, left_1, right_1))
              case CoqListType(elem, _) =>
                ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpSetEq, left_1, right_1))
              case ProofTypes.CoqPtrType => ??? // TODO: Handle pointer equality? or fail?
            }
          case Expressions.OpGt =>
            ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpLeq, left_1, right_1))
          case Expressions.OpGeq =>
            ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpLt, left_1, right_1))
          case Expressions.OpOverloadedPlus =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqPtrType => ??? // TODO: handle pointer equality or fail?
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpPlus, left_1, right_1)
              case CoqListType(elem, _) =>
                ProofCBinaryExpr(ProofCOpUnion, left_1, right_1)
            }
          case Expressions.OpOverloadedMinus =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqPtrType => ??? // TODO: handle pointer equality or fail?
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpMinus, left_1, right_1)
              case CoqListType(elem, _) =>
                ProofCBinaryExpr(ProofCOpDiff, left_1, right_1)
            }
          case Expressions.OpOverloadedLeq =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqPtrType => ??? // TODO: handle pointer equality or fail?
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpLeq, left_1, right_1)
              case CoqListType(elem, _) =>
                ProofCBinaryExpr(ProofCOpSubset, left_1, right_1)
            }
          case Expressions.OpOverloadedStar => ??? // TODO: Handle star operation
        }

    }
  }


  /** given a VST proof expression and a typing context,
    * this function will type the expression and return
    * a type */
  def type_expr(context: Map[Ident, VSTProofType]) (cvalue: ProofTerms.Expressions.ProofCExpr) : VSTProofType =
    cvalue match {
      case ProofCVar(name, typ) => typ
      case ProofCIntConst(value) => CoqIntType
      case ProofCSetLiteral(elems) => CoqListType(type_expr(context)(elems.head), Some (elems.length))
      case ProofCIfThenElse(cond, left, right) => type_expr(context)(left)
      case ProofCBinaryExpr(op, left, right) => op match {
        case ProofCOpPlus => CoqIntType
        case ProofCOpMinus => CoqIntType
        case ProofCOpMultiply => CoqIntType
      }
      case ProofCUnaryExpr(op, e) => op match {
        case ProofCOpUnaryMinus => CoqIntType
      }
    }

  /**
    * Translate a list of suslik heaplets into a form accepted by VST
    * @param context the typing context
    * @param heaplets a list of suslik heaplets
    * @return a VST encoding of these heaplets
    *
    * Note: Suslik encodes blocks of pointers slightly differently to
    * VST - when dealing with a block of contiguous pointers in memory,
    * Suslik first uses a block declaration to specify the size of the
    * contiguous block, and then has a number of subsequent heaplets
    * that assign values to each element of this block.
    *
    * VST combines these two declarations into one: `data_at` - a `data_at` declaration
    * states what a given pointer points to - in the case of contiguous memory,
    * we must list out the corresponding values in order - just as they would be encoded in memory
    *
    * This function performs the translation between suslik's encoding and VST's encoding
    */
  def translate_heaplets(context: Map[Ident, VSTProofType])(heaplets: List[Heaplet]): List[VSTHeaplet] = {
    val initial_map: Map[Ident, (List[PointsTo], Option[Block])] = Map.empty

    // we first build up a mapping from pointer variables
    // to the declarations that relate to them
    // predicate applications are separated out unchanged
    // as these translate directly to vst
    val (map: Map[Ident, (List[PointsTo], Option[Block])], apps): (Map[Ident, (List[PointsTo], Option[Block])], List[CSApp]) =
      heaplets.foldLeft((initial_map, List(): List[CSApp]))({
        case ((map, acc), ty: Heaplet) =>
          ty match {
            case ty@PointsTo(loc@Var(name), offset, value) =>
              val updated_map = map.get(name) match {
                case None => map.updated(name, (List(ty), None))
                case Some((points_to_acc: List[_], block_acc)) =>
                  map.updated(name, (List(ty) ++ points_to_acc, block_acc))
              }
              (updated_map, acc: List[CSApp])
            case ty@Block(loc@Var(name), sz) =>
              val updated_map = map.get(name) match {
                case None => map.updated(name, (List(), Some(ty)))
                case Some((points_to_acc, None)) => map.updated(name, (points_to_acc, Some(ty)))
              }
              (updated_map, acc: List[CSApp])
            case SApp(pred, args, tag, card) =>
              (map, (List(CSApp(pred, args.map(translate_expression((context))), translate_expression(context)(card))) ++ acc)
              )
          }
      })

    // having built the mapping, we then translate each (k,v) pair in this
    // mapping into a VST Data at declaration
    val blocks: List[CDataAt] = map.map({ case (var_nam, (points_to, o_block)) =>
      o_block match {
        case Some((_@Block(loc,sz))) =>
          val loc_pos = translate_expression(context)(loc)
          val o_array : Array[Option[ProofCExpr]] = Array.fill(sz)(None)
          points_to.foreach({case PointsTo(_, offset, value) =>
              o_array.update(offset, Some(translate_expression(context)(value)))
          })
          val elems = o_array.map(_.get).toList
          val elem_type = type_expr(context)(elems.head)
          CDataAt(loc_pos, CoqListType(elem_type, Some(sz)), sz, ProofCSetLiteral(elems))
        case None =>
          assert(
            points_to.length == 1,
            "found multiple points to information (i.e x :-> 1, (x + 1) :-> 2) for a variable without an associated block"
          )
          (points_to.head : PointsTo) match {
            case PointsTo(loc, 0, value) =>
              val c_value = translate_expression(context)(value)
              CDataAt(translate_expression(context)(loc), type_expr(context)(c_value), 0, c_value)
            case PointsTo(_, _, _) =>
              assert(false, "found points to information without a block that references a non-zero element (i.e (x + 1) :-> 2)")
              ???
          }
      }
    }).toList

    // return the blocks and the applications
    blocks.map(_.asInstanceOf[VSTHeaplet]) ++ apps.map(_.asInstanceOf[VSTHeaplet])
  }
  def translate_assertion (context: Map[Ident, VSTProofType]) (assertion: Assertion): FormalCondition = assertion match {
    case Assertion(phi, sigma) =>
    {
      val pure_conditions =
        phi.conjuncts.map(translate_expression(context))
          .map(IsTrueProp).toList

      val spatial_conditions: List[VSTHeaplet] =
        translate_heaplets(context)(sigma.chunks)

      FormalCondition(pure_conditions, spatial_conditions)
    }
  }

  /** translates a Suslik function specification into a proof */
  def translate_conditions(proc: CProcedureDefinition)(goal: Goal): (FormalSpecification, Map[Ident, VSTProofType]) = {

    val name: Ident = proc.name
    val c_params: Seq[(Ident, VSTCType)] = proc.params.map({ case (CVar(name), cType) => (name, cType) })


    // collect all cardinality_params and their associated types
    val cardinality_params: Map[String, CoqCardType] = (goal.pre.sigma.chunks ++ goal.post.sigma.chunks).flatMap({
      case PointsTo(loc, offset, value) => None
          case Block(loc, sz) => None
          case SApp(pred, args, tag, Var(name)) => Some(name, CoqCardType(pred))
          case _ => throw TranslationException("ERR: Expecting all predicate applications to be abstract variables")
    }).toMap

    val formal_params: List[(Ident, VSTProofType)] = {
      val c_param_set = c_params.map(_._1).toSet
      goal.universals
        .map({ case variable@Var(name) =>
        if (cardinality_params.contains(name)) {
          (name, cardinality_params(name))
        } else {
          (name, translate_type(goal.gamma(variable)))
        }})
        .filterNot({case (name, _) =>  c_param_set.contains(name)}).toList
    }

    val existential_params: List[(Ident, VSTProofType)] =
      goal.existentials.map({ case variable@Var(name) =>
        if (cardinality_params.contains(name)) {
          (name, cardinality_params(name))
        } else {
          (name, translate_type(goal.gamma(variable)))
        }
      }).toList
    val return_type: VSTCType = proc.rt

    val context = (
      formal_params ++ existential_params ++
        c_params.map({ case (ident, cType) => (ident, ProofTypes.proof_type_of_c_type(cType)) })
      ).toMap

    val precondition: FormalCondition = {
      val pure_conditions =
        goal.pre.phi.conjuncts.map(translate_expression(context))
          .map(IsTrueProp).toList ++ (c_params).flatMap({ case (ident, cType) =>
          cType match {
            case CTypes.CIntType => Some(IsValidInt(CVar(ident)))
            case CTypes.CUnitType => None
            case CTypes.CVoidPtrType => Some(IsValidPointerOrNull(CVar(ident)))
          }
      }) ++ formal_params.flatMap({ case (ident, ty) => ty match {
          case ProofTypes.CoqPtrType =>Some(IsValidPointerOrNull(CVar(ident)))
          case ProofTypes.CoqIntType => Some(IsValidInt(CVar(ident)))
          case _ => None
        }})
      val spatial_conditions: List[VSTHeaplet] =
        translate_heaplets(context)(goal.pre.sigma.chunks)

      FormalCondition(pure_conditions, spatial_conditions)
    }
    val postcondition: FormalCondition = {
      val pure_conditions =
        goal.post.phi.conjuncts.map(translate_expression(context))
          .map(IsTrueProp).toList
      val spatial_conditions =
        translate_heaplets(context)(goal.post.sigma.chunks)
        // goal.post.sigma.chunks.map(translate_heaplet(context)).toList
      FormalCondition(pure_conditions, spatial_conditions)
    }

    (FormalSpecification(
      name, c_params, formal_params, existential_params, precondition, postcondition, return_type
    ), context)
  }


  /** convert a list of cardinality relations (child, parent) (i.e child < parent) into a map
    * from cardinality name to constructors */
  def build_card_cons(card_conds: List[(String, String)]): Map[String, CardOf] = {
    // to perform this translation, we first construct a mapping of relations
    // where for every constraint of the form (a < b), we set map(b) = a :: map(b),
    // thus the mapping for a variable contains the list of other variables that are
    // constrainted to be immediately smaller than it
    var child_map : Map[String, List[String]] = Map.empty
    card_conds.foreach({case (child, parent) =>
    child_map.get(parent) match {
            case None => child_map = child_map.updated(parent, List(child))
            case Some(children) => child_map = child_map.updated(parent, child :: children)
    }})
    // the keys of the map now become variables that are destructured
    // in the match case to produce the variables immediately below it
    child_map.map({ case (str, strings) => (str, CardOf(strings))})
  }


  /** translates suslik's inductive predicate into a format that is
    * accepted by VST
    *
    * In order to do this, we make use of the cardinality constraints that are
    * associated with each clause, and use this to construct an inductive data
    * type that encodes the proof of termination
    *
    * For example, consider the lseg predicate
    *
    * lseg(x, s) {
    *
    *  x == 0 ==> ... (no cardinality constraints)
    *
    *  x <> 0 ==> a < self_card ... lseg(x',s')<a>
    *
    * }
    *
    * Then we'd create a cardinality datatype as:
    *
    * Inductive lseg_card : Set :=
    *
    *   | lseg_card_0 : lseg_card
    *
    *   | lseg_card_1 : lseg_card -> lseg_card.
    *
    * And then implement lseg as taking in a third parameter being its cardinality,
    * and matching on this - taking the first clause if the input is `lseg_card0` and the
    * second clause if the input is `lseg_card1 a` (and recursing on `a`
    *
    * */
  def translate_predicate(env: Environment)(predicate: InductivePredicate): VSTPredicate = {


    // Determines whether a given variable is a cardinality constraint
    // TODO: I've definitely seen some function elsewhere that already does this
    def is_card (s: String) : Boolean = s.startsWith("_") || s.contentEquals("self_card")

    // extracts a cardinality relation from an expression if it exists
    def extract_card_constructor(expr: Expressions.Expr) : Option[(String, String)] = {
      expr match {
        case Expressions.BinaryExpr(op, Var(left), Var(parent))
        if is_card(left) && is_card(parent) =>
          op match {
            case op: Expressions.RelOp => op match {
              case Expressions.OpLt =>
                Some ((left, parent))
              case _ => None
            }
            case _ => None
          }
        case Expressions.OverloadedBinaryExpr(overloaded_op, Var(left), Var(parent))
        if is_card(left) && is_card(parent) =>
          overloaded_op match {
            case op: Expressions.BinOp => op match {
              case op: Expressions.RelOp => op match {
                case Expressions.OpLt => Some ((left, parent))
                case _ => None
              }
              case _ => None
            }
            case Expressions.OpGt =>Some ((parent, left))
            case _ => None
          }
        case _ => None
      }

    }

    // base context contains type information for every variable used in the
    // predicate (even if it occurs at a top level or not)
    val base_context : List[(Ident, VSTProofType)] = {
      var gamma: Gamma = Map.empty
      predicate match {
        case InductivePredicate(name, params, clauses) =>
          clauses.foreach({case InductiveClause(selector, assn) =>
            selector.resolve(gamma, Some(BoolType)).foreach(v => gamma = v)
            assn.phi.conjuncts.foreach(expr =>
              expr.resolve(gamma, Some(BoolType)).foreach(v => gamma = v)
            )
            assn.sigma.resolve(gamma, env).foreach(v => gamma = v)
          })
      }
      gamma.map({case (Var(name), ty) => (name, translate_type(ty))}).toList
    }

    predicate match {
      case InductivePredicate(name, raw_params, raw_clauses) => {

        val params: List[(String, VSTProofType)] =
          raw_params.map({case (Var(name), sType) => (name, translate_type(sType))})
        val context: Map[Ident, VSTProofType] = (base_context ++ params).toMap


        // separate clauses by cardinality constructors
        // NOTE: here we assume that cardinality constructors are unique - i.e each clause maps to a
        // unique cardinality constraint
        val clauses: Map[CardConstructor, VSTPredicateClause] = raw_clauses.map({
          case InductiveClause(selector, asn) =>
            // first, split the pure conditions in the predicate between those that
            // encode cardinality constraints and those that don't
            val (r_conds, r_card_conds) = asn.phi.conjuncts.map(expr =>
              extract_card_constructor(expr) match {
                case value@Some(_) => (None, value)
                case None => (Some(expr), None)
              }
            ).toList.unzip

            // translate the pure conditions into VST format
            val select = translate_expression(context)(selector)
            val conds = r_conds.flatten.map(translate_expression(context)).toList

            // translate the spatial constraints
            val spat_conds = translate_heaplets(context)(asn.sigma.chunks.toList)

            // Convert the cardinality constraints into an associated constructor
            val card_conds = r_card_conds.flatten
            card_conds match {
              case card_conds@(::(_, _)) =>
                val card_cons : Map[String, CardConstructor] = build_card_cons(card_conds)
                (card_cons("self_card"), VSTPredicateClause(select :: conds, spat_conds, card_cons))
              case Nil => (CardNull, VSTPredicateClause(select :: conds, spat_conds, Map.empty))
            }
        }).toMap
        VSTPredicate(name, params, base_context, clauses)
      }
    }
  }
}
