package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.targets.vst.Types
import org.tygus.suslik.certification.targets.vst.Types.{CoqCardType, CoqIntSetType, CoqIntValType, CoqPtrValType, CoqZType, VSTCType, VSTType}
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Expressions.{ProofCBinOp, ProofCBinaryExpr, ProofCBoolConst, ProofCCardinalityConstructor, ProofCExpr, ProofCIfThenElse, ProofCIntConst, ProofCIntSetLiteral, ProofCNullval, ProofCOpAnd, ProofCOpBoolEq, ProofCOpDiff, ProofCOpImplication, ProofCOpIn, ProofCOpIntValEq, ProofCOpIntersect, ProofCOpLeq, ProofCOpLt, ProofCOpMinus, ProofCOpMultiply, ProofCOpNot, ProofCOpOr, ProofCOpPlus, ProofCOpPtrValEq, ProofCOpSetEq, ProofCOpSubset, ProofCOpUnaryMinus, ProofCOpUnion, ProofCOpZEq, ProofCUnOp, ProofCUnaryExpr, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CDataAt, CSApp, VSTHeaplet}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{CardConstructor, CardNull, CardOf, FormalCondition, FormalSpecification, IsTrueProp, IsValidInt, IsValidPointerOrNull, VSTPredicate, VSTPredicateClause}
import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.{BoolType, CardType, Expressions, Ident, IntSetType, IntType, LocType, SSLType}
import org.tygus.suslik.logic.{Block, Environment, FunSpec, Gamma, Heaplet, InductiveClause, InductivePredicate, PointsTo, PredicateEnv, SApp}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}


/** translates suslik proof terms to VST compatible proof terms  */
object  ProofSpecTranslation {

  def to_ssl_context(gamma: Map[String, VSTType]) : Gamma = {
    def to_ssl_type(ty: VSTType) : SSLType = ty match {
      case cType: VSTCType => cType match {
        case Types.CoqPtrValType => LocType
        case Types.CoqIntValType => IntType
      }
      case Types.CoqZType => IntType
      case Types.CoqIntSetType => IntSetType
      case CoqCardType(pred_type) => CardType
    }
    gamma.map({case (name, ty) => (Var(name), to_ssl_type(ty))})
  }

  /** Translates a cardinality to a vst expression that can be passed around  */
  def translate_cardinality(predicate: VSTPredicate, cardinality: CardConstructor): ProofCExpr = {
    ProofCCardinalityConstructor(
      predicate.name,
      predicate.constructor_name(cardinality),
      cardinality match {
        case ProofTerms.CardNull => List()
        case CardOf(args) => args.map(arg => ProofCVar(arg, CoqCardType(predicate.name)))
      }
    )
  }

  /** translate a suslik type into a VST proof type */
  def translate_predicate_param_type(lType: SSLType): VSTType =
    lType match {
      case IntType => CoqZType
      case LocType => CoqPtrValType
      case IntSetType => CoqIntSetType
      case _ => throw TranslationException("Attempted to translate ssl type of invalid form into VST Type")
    }


  /** translate a suslik expression into a VST proof expression (note: this is not the same as a VST C expression, so can support terms like list comparisons etc.)
    * */
  def translate_expression(context: Map[Ident, VSTType])(expr: Expressions.Expr, target: Option[VSTType]=None): ProofCExpr = {
    def type_expr(left_1: ProofCExpr): VSTType = left_1.type_expr
    def translate_binop(op: Expressions.BinOp)(ty: VSTType): ProofCBinOp = {
      op match {
        case op: Expressions.RelOp => (op, ty) match {
          case (Expressions.OpEq, CoqIntValType) => ProofCOpIntValEq
          case (Expressions.OpEq, CoqZType) => ProofCOpZEq
          case (Expressions.OpEq, CoqPtrValType) => ProofCOpPtrValEq
          case (Expressions.OpBoolEq, _) => ProofCOpBoolEq
          case (Expressions.OpLeq, _) => ProofCOpLeq
          case (Expressions.OpLt, _) => ProofCOpLt
          case (Expressions.OpIn, _) => ProofCOpIn
          case (Expressions.OpSetEq, _) => ProofCOpSetEq
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


    expr.resolveOverloading(to_ssl_context(context)) match {
      case const: Expressions.Const => const match {
        case Expressions.IntConst(value) => target match {
          case Some(CoqPtrValType) => ProofCNullval
          case _ => ProofCIntConst(value)
        }
        case Expressions.LocConst(value) if value == 0 => ProofCNullval
        case Expressions.BoolConst(value) => ProofCBoolConst(value)
      }
      case Var(name) => ProofCVar(name, context(name))
      case Expressions.SetLiteral(elems) => ProofCIntSetLiteral(elems.map(v => translate_expression(context)(v, Some(CoqIntSetType))))
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
        ProofCBinaryExpr(top, left_expr, translate_expression(context)(right, target=Some(type_of_expr)))
      case Expressions.IfThenElse(cond, left, right) =>
        val left_expr = translate_expression(context)(left)
        val l_type_1 = type_expr(left_expr)
        ProofCIfThenElse(
          translate_expression(context)(cond), left_expr,
          translate_expression(context)(right, target=Some(l_type_1))
        )
    }
  }


  /** given a VST proof expression and a typing context,
    * this function will type the expression and return
    * a type */
  def type_expr(context: Map[Ident, VSTType])(cvalue: ProofCExpr): VSTType = cvalue.type_expr

  /**
    * Translate a list of suslik heaplets into a form accepted by VST
    *
    * @param context  the typing context
    * @param heaplets a list of suslik heaplets
    * @return a VST encoding of these heaplets
    *
    *         Note: Suslik encodes blocks of pointers slightly differently to
    *         VST - when dealing with a block of contiguous pointers in memory,
    *         Suslik first uses a block declaration to specify the size of the
    *         contiguous block, and then has a number of subsequent heaplets
    *         that assign values to each element of this block.
    *
    *         VST combines these two declarations into one: `data_at` - a `data_at` declaration
    *         states what a given pointer points to - in the case of contiguous memory,
    *         we must list out the corresponding values in order - just as they would be encoded in memory
    *
    *         This function performs the translation between suslik's encoding and VST's encoding
    */
  def translate_heaplets(context: Map[Ident, VSTType])(heaplets: List[Heaplet]): List[VSTHeaplet] = {
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
            (map, (List(CSApp(pred, args.map(v => translate_expression((context))(v)), translate_expression(context)(card))) ++ acc)
            )
        }
    })

    // having built the mapping, we then translate each (k,v) pair in this
    // mapping into a VST Data at declaration
    val blocks: List[CDataAt] = map.map({ case (var_nam, (points_to, o_block)) =>
      o_block match {
        case Some((_@Block(loc, sz))) =>
          val loc_pos = translate_expression(context)(loc)
          val o_array: Array[Option[ProofCExpr]] = Array.fill(sz)(None)
          points_to.foreach({ case PointsTo(_, offset, value) =>
            o_array.update(offset, Some(translate_expression(context)(value)))
          })
          val elems = o_array.map(_.get).toList
          CDataAt(loc_pos, elems)
        case None =>
          if(points_to.length != 1) {
            throw TranslationException("found multiple points to information (i.e x :-> 1, (x + 1) :-> 2) for a variable without an associated block")
          }

          (points_to.head: PointsTo) match {
            case PointsTo(loc, 0, value) =>
              val c_value = translate_expression(context)(value)
              CDataAt(translate_expression(context)(loc), List(c_value))
            case PointsTo(_, _, _) =>
              throw TranslationException("found points to information without a block that references a non-zero element (i.e (x + 1) :-> 2)")
          }
      }
    }).toList

    // return the blocks and the applications
    blocks.map(_.asInstanceOf[VSTHeaplet]) ++ apps.map(_.asInstanceOf[VSTHeaplet])
  }

  def translate_assertion(context: Map[Ident, VSTType])(assertion: Assertion): FormalCondition = assertion match {
    case Assertion(phi, sigma) => {
      val pure_conditions =
        phi.conjuncts.map(v => translate_expression(context)(v))
          .map(IsTrueProp).toList

      val spatial_conditions: List[VSTHeaplet] =
        translate_heaplets(context)(sigma.chunks)

      FormalCondition(pure_conditions, spatial_conditions)
    }
  }

  def proof_type_of_c_type(cType: VSTType): VSTCType = cType match {
    case cType: Types.VSTCType => cType
    case _ => throw TranslationException(s"Attempt to create proof type of invalid term ${cType.pp}")
  }

  /** translates a Suslik function specification into a proof */
  def translate_conditions(name: String, c_params: List[(Ident, VSTCType)])(goal: Goal): (FormalSpecification, Map[Ident, VSTType]) = {

    // collect all cardinality_params and their associated types
    val cardinality_params: Map[String, CoqCardType] = (goal.pre.sigma.chunks ++ goal.post.sigma.chunks).flatMap({
      case PointsTo(loc, offset, value) => None
      case Block(loc, sz) => None
      case SApp(pred, args, tag, Var(name)) => Some(name, CoqCardType(pred))
      case _ => throw TranslationException("ERR: Expecting all predicate applications to be abstract variables")
    }).toMap

    val formal_params: List[(Ident, VSTType)] = {
      val c_param_set = c_params.map(_._1).toSet
      goal.universals
        .map({ case variable@Var(name) =>
          if (cardinality_params.contains(name)) {
            (name, cardinality_params(name))
          } else {
            (name, translate_predicate_param_type(goal.gamma(variable)))
          }
        })
        .filterNot({ case (name, _) => c_param_set.contains(name) }).toList
    }

    val existential_params: List[(Ident, VSTType)] =
      goal.existentials.map({ case variable@Var(name) =>
        if (cardinality_params.contains(name)) {
          (name, cardinality_params(name))
        } else {
          (name, translate_predicate_param_type(goal.gamma(variable)))
        }
      }).toList

    val context = (
      formal_params ++ existential_params ++
        c_params.map({ case (ident, cType) => (ident, proof_type_of_c_type(cType)) })
      ).toMap

    val precondition: FormalCondition = {
      val pure_conditions =
        goal.pre.phi.conjuncts.map(v => translate_expression(context)(v))
          .map(IsTrueProp).toList ++ (c_params).flatMap({ case (ident, cType) =>
          cType match {
            case CoqIntValType => Some(IsValidInt(ident))
            case CoqPtrValType => Some(IsValidPointerOrNull(ident))
            case _ => None
          }
        }) ++ formal_params.flatMap({ case (ident, ty) => ty match {
          case CoqPtrValType => Some(IsValidPointerOrNull(ident))
          case CoqIntValType => Some(IsValidInt(ident))
          case _ => None
        }
        })
      val spatial_conditions: List[VSTHeaplet] =
        translate_heaplets(context)(goal.pre.sigma.chunks)

      FormalCondition(pure_conditions, spatial_conditions)
    }
    val postcondition: FormalCondition = {
      val pure_conditions =
        goal.post.phi.conjuncts.map(v => translate_expression(context)(v))
          .map(IsTrueProp).toList
      val spatial_conditions =
        translate_heaplets(context)(goal.post.sigma.chunks)
      // goal.post.sigma.chunks.map(translate_heaplet(context)).toList
      FormalCondition(pure_conditions, spatial_conditions)
    }

    (FormalSpecification(
      name, c_params, formal_params, existential_params, precondition, postcondition
    ), context)
  }


  /** convert a list of cardinality relations (child, parent) (i.e child < parent) into a map
    * from cardinality name to constructors */
  def build_card_cons(card_conds: List[(String, String)]): Map[String, CardOf] = {
    // to perform this translation, we first construct a mapping of relations
    // where for every constraint of the form (a < b), we set map(b) = a :: map(b),
    // thus the mapping for a variable contains the list of other variables that are
    // constrainted to be immediately smaller than it
    var child_map: Map[String, List[String]] = Map.empty
    card_conds.foreach({ case (child, parent) =>
      child_map.get(parent) match {
        case None => child_map = child_map.updated(parent, List(child))
        case Some(children) => child_map = child_map.updated(parent, child :: children)
      }
    })
    // the keys of the map now become variables that are destructured
    // in the match case to produce the variables immediately below it
    child_map.map({ case (str, strings) => (str, CardOf(strings)) })
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
    * x == 0 ==> ... (no cardinality constraints)
    *
    * x <> 0 ==> a < self_card ... lseg(x',s')<a>
    *
    * }
    *
    * Then we'd create a cardinality datatype as:
    *
    * Inductive lseg_card : Set :=
    *
    * | lseg_card_0 : lseg_card
    *
    * | lseg_card_1 : lseg_card -> lseg_card.
    *
    * And then implement lseg as taking in a third parameter being its cardinality,
    * and matching on this - taking the first clause if the input is `lseg_card0` and the
    * second clause if the input is `lseg_card1 a` (and recursing on `a`
    *
    **/
  def translate_predicate(env: Environment)(predicate: InductivePredicate): VSTPredicate = {


    // Determines whether a given variable is a cardinality constraint
    // TODO: I've definitely seen some function elsewhere that already does this
    def is_card(s: String): Boolean = s.startsWith("_") || s.contentEquals("self_card")

    // extracts a cardinality relation from an expression if it exists
    def extract_card_constructor(expr: Expressions.Expr): Option[(String, String)] = {
      expr match {
        case Expressions.BinaryExpr(op, Var(left), Var(parent))
          if is_card(left) && is_card(parent) =>
          op match {
            case op: Expressions.RelOp => op match {
              case Expressions.OpLt =>
                Some((left, parent))
              case _ => None
            }
            case _ => None
          }
        case Expressions.OverloadedBinaryExpr(overloaded_op, Var(left), Var(parent))
          if is_card(left) && is_card(parent) =>
          overloaded_op match {
            case op: Expressions.BinOp => op match {
              case op: Expressions.RelOp => op match {
                case Expressions.OpLt => Some((left, parent))
                case _ => None
              }
              case _ => None
            }
            case Expressions.OpGt => Some((parent, left))
            case _ => None
          }
        case _ => None
      }
    }

    // base context contains type information for every variable used in the
    // predicate (even if it occurs at a top level or not)
    val base_context: List[(Ident, VSTType)] = {
      var (pred_name, gamma) = predicate match {
        case InductivePredicate(name, params, clauses) =>
          val pred_name = name
          val gamma = clauses.foldLeft(params.toMap)({ case (base_gamma, InductiveClause(selector, asn)) =>
            var gamma = selector.resolve(base_gamma, Some(BoolType)).getOrElse(base_gamma) ++ base_gamma
            gamma = asn.phi.conjuncts.foldLeft(gamma)({ case (gamma, expr) => expr.resolve(gamma, Some(BoolType)).getOrElse(gamma) }) ++ base_gamma

            asn.sigma.resolve(gamma, env).getOrElse(gamma) ++ base_gamma
          })
          (pred_name, gamma)
      }
      gamma.map({ case (Var(name), ty) => (name, ty match {
        case CardType => CoqCardType(pred_name)
        case _ => translate_predicate_param_type(ty)
      })
      }).toList
    }

    predicate match {
      case InductivePredicate(name, raw_params, raw_clauses) => {

        val params: List[(String, VSTType)] =
          raw_params.map({ case (Var(name), sType) => (name, translate_predicate_param_type(sType)) })
        val context: Map[Ident, VSTType] = (base_context ++ params).toMap


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
            val conds = r_conds.flatten.map(v => translate_expression(context)(v)).toList

            // translate the spatial constraints
            val spat_conds = translate_heaplets(context)(asn.sigma.chunks.toList)

            // Convert the cardinality constraints into an associated constructor
            val card_conds = r_card_conds.flatten
            card_conds match {
              case card_conds@(::(_, _)) =>
                val card_cons: Map[String, CardConstructor] = build_card_cons(card_conds)
                (card_cons("self_card"), VSTPredicateClause(select :: conds, spat_conds, card_cons))
              case Nil => (CardNull, VSTPredicateClause(select :: conds, spat_conds, Map.empty))
            }
        }).toMap
        VSTPredicate(name, params, base_context, clauses)
      }
    }
  }
}
