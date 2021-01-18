package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.CTypes.VSTCType
import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.clang.{CTypes, PrettyPrinting}
import org.tygus.suslik.certification.targets.vst.logic.Formulae.VSTHeaplet
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.Expressions.{ProofCExpr, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.{CoqBoolType, CoqCardType, CoqIntType, CoqListType, CoqParamType, VSTProofType}
import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.language.Ident
import org.tygus.suslik.logic.SApp

object ProofTerms {

  sealed abstract class PureFormula extends PrettyPrinting

  /** predicate encoding that C-parameter (of type val) is a valid pointer */
  case class IsValidPointerOrNull(name: CVar) extends PureFormula {
    override def pp: String =
      s"is_pointer_or_null(${name.pp})"
  }

  /** predicate encoding that C-parameter (of type val) is a valid int */
  case class IsValidInt(name: CVar) extends PureFormula {
    override def pp: String =
      s"ssl_is_valid_int(${name.pp})"
  }

  /** Redefinition of expressions for use in VST proofs
    **/
  object Expressions {

    /** encoding of expressions in VST proof script
      * By default any boolean value will print to prop
      * use pp_as_bool_value to print as a boolean
      */
    sealed abstract class ProofCExpr extends PrettyPrinting {

      /** Applies a substitution to an expression */
      def subst(mapping: Map[String, ProofCExpr]): ProofCExpr = this match {
        case expr@ProofCVar(name, _) => mapping.get(name) match {
          case Some(value) => value.subst(mapping)
          case None => expr
        }
        case expr@ProofCBoolConst(_) => expr
        case expr@ProofCIntConst(_, _) => expr
        case ProofCSetLiteral(elems) =>
          ProofCSetLiteral(elems.map(_.subst(mapping)))
        case ProofCIfThenElse(cond, left, right) =>
          ProofCIfThenElse(cond.subst(mapping), left.subst(mapping), right.subst(mapping))
        case ProofCBinaryExpr(op, left, right) =>
          ProofCBinaryExpr(op, left.subst(mapping), right.subst(mapping))
        case ProofCUnaryExpr(op, e) =>
          ProofCUnaryExpr(op, e.subst(mapping))
        case ProofCCardinalityConstructor(pred_type, name, args) =>
          ProofCCardinalityConstructor(pred_type, name, args.map(_.subst(mapping)))
      }

      def type_expr: VSTProofType = this match {
        case ProofCVar(name, typ) => typ
        case ProofCBoolConst(value) => CoqBoolType
        case ProofCIntConst(value, false) => CoqIntType
        case ProofCIntConst(value, true) => CoqParamType(CTypes.CVoidPtrType)
        case ProofCSetLiteral(elems) => CoqListType(elems.head.type_expr, Some(elems.length))
        case ProofCIfThenElse(cond, left, right) => left.type_expr
        case ProofCBinaryExpr(op, left, right) => op match {
          case ProofCOpPlus => CoqIntType
          case ProofCOpMinus => CoqIntType
          case ProofCOpMultiply => CoqIntType
          case _ => CoqBoolType
        }
        case ProofCUnaryExpr(op, e) => e.type_expr
        case ProofCCardinalityConstructor(pred_type, _, _) => CoqCardType(pred_type)
      }

      /** prints the expression as though it were an element
        * of type val (vst's encoding of C-values)
        */
      def pp_as_c_value: String = this match {
        case ProofCVar(name, typ) => typ match {
          case ProofTypes.CoqParamType(ty) => name
          case ProofTypes.CoqPtrType => name
          case ProofTypes.CoqIntType => s"(Vint (Int.repr ${name}))"
          case ProofTypes.CoqListType(elem, length) => name
          case ProofTypes.CoqCardType(_) => throw TranslationException("Error: inconsistent assumptions, attempting to print a cardinality as a c type")
        }
        case ProofCIntConst(value, false) => s"(Vint (Int.repr ${value.toString}))"
        case ProofCSetLiteral(elems) =>
          s"[${elems.map(_.pp_as_c_value).mkString("; ")}]"
        case value@ProofCBinaryExpr(op, _, _) =>
          val is_int = op match {
            case ProofCOpPlus => true
            case ProofCOpMinus => true
            case ProofCOpMultiply => true
            case _ => false
          }
          if (is_int) {
            s"(Vint (Int.repr ${value.pp}))"
          } else {
            value.pp
          }
        case value@ProofCUnaryExpr(op, _) => op match {
          case ProofCOpNot => value.pp
          case ProofCOpUnaryMinus => s"(Vint (Int.repr ${value.pp}))"
        }
        case v => v.pp
      }

      def pp_as_ssl_union_value: String = this match {
        case ProofCVar(name, typ) => typ match {
          case ProofTypes.CoqParamType(ty) => ty match {
            case CTypes.CIntType => s"inl ${name}"
            case CTypes.CVoidPtrType => s"inl ${name}"
          }
          case ProofTypes.CoqPtrType => s"inr ${name}"
          case ProofTypes.CoqIntType => s"inl (Vint (Int.repr ${name}))"
          case ProofTypes.CoqListType(elem, length) => name
          case ProofTypes.CoqCardType(_) => throw TranslationException("Error: inconsistent assumptions, attempting to print a cardinality as a c type")
        }
        case ProofCIntConst(value, false) => s"inl (Vint (Int.repr ${value.toString}))"
        case ProofCIntConst(0, true) => s"inr nullval"
        case ProofCSetLiteral(elems) =>
          s"[${elems.map(_.pp_as_ssl_union_value).mkString("; ")}]"
        case value@ProofCBinaryExpr(op, _, _) =>
          val is_int = op match {
            case ProofCOpPlus => true
            case ProofCOpMinus => true
            case ProofCOpMultiply => true
            case _ => false
          }
          if (is_int) {
            s"inl (Vint (Int.repr ${value.pp}))"
          } else {
            throw TranslationException("Error: inconsistent assumptions, attempting to print an arithmetic operation on non-integral values as a c expression.")
          }
        case value@ProofCUnaryExpr(op, _) => op match {
          case ProofCOpUnaryMinus => s"inl (Vint (Int.repr ${value.pp}))"
        }
        case v => v.pp
      }

      def pp_as_bool_value: String = this match {
        case value@ProofCBinaryExpr(op, expr_a, expr_b) =>
          op match {
            case ProofCOpImplication => s"(implb ${expr_a.pp_as_bool_value} ${expr_b.pp_as_bool_value})"
            case ProofCOpIntEq => s"(Nat.eqb ${expr_a.pp} ${expr_b.pp})"
            case ProofCOpBoolEq => s"(eqb ${expr_a.pp} ${expr_b.pp})"
            case ProofCOpLeq => s"(Z.leb ${expr_a.pp} ${expr_b.pp})"
            case ProofCOpLt => s"(Z.ltb ${expr_a.pp} ${expr_b.pp})"
            case ProofCOpAnd => s"(andb ${expr_a.pp_as_bool_value} ${expr_b.pp_as_bool_value})"
            case ProofCOpOr => s"(orb ${expr_a.pp_as_bool_value} ${expr_b.pp_as_bool_value})"
            case ProofCOpIn => ??? // TODO: how to handle in operations? don't seem to show up in proofs
            case ProofCOpSetEq => ??? // TODO: see above
            case ProofCOpPtrEq => ??? // TODO: ditto
          }
        case value@ProofCUnaryExpr(op, _) => op match {
          case ProofCOpNot => value.pp
        }
      }

      def pp_as_int_value: String = this match {
        case ProofCVar(name, typ) => typ match {
          case ProofTypes.CoqParamType(CTypes.CIntType) => s"(force_signed_int ${name})"
          case ProofTypes.CoqIntType => s"${name}"
        }
        case ProofCIntConst(value, is_ptr) => value.toString
        case ProofCIfThenElse(cond, left, right) => s"(if ${cond.pp_as_bool_value} then ${left.pp_as_int_value} else  ${right.pp_as_int_value})"
        case ProofCBinaryExpr(op, left, right) => op match {
          case ProofCOpPlus => s"(${left.pp_as_int_value} + ${right.pp_as_int_value})"
          case ProofCOpMinus => s"(${left.pp_as_int_value} - ${right.pp_as_int_value})"
          case ProofCOpMultiply => s"(${left.pp_as_int_value} * ${right.pp_as_int_value})"
          case ProofCOpIntEq => s"(${left.pp_as_int_value} =? ${right.pp_as_int_value})"
          case ProofCOpLeq => s"(${left.pp_as_int_value} <=? ${right.pp_as_int_value})"
          case ProofCOpLt => s"(${left.pp_as_int_value} <? ${right.pp_as_int_value})"
        }
        case ProofCUnaryExpr(op, e) => op match {
          case ProofCOpUnaryMinus => s"(- ${e.pp_as_int_value})"
        }
      }


      /** print as a pointer value
        *
        * @throws NotImplementedError if expression is not a variable or 0-int */
      def pp_as_ptr_value: String = this match {
        case ProofCVar(name, typ) => name
        case ProofCBoolConst(value) => this.pp
        case ProofCIntConst(value, _) => if (value == 0) {
          "nullval"
        } else {
          this.pp
        }
        case ProofCSetLiteral(elems) => this.pp
        case ProofCIfThenElse(cond, left, right) => this.pp
        case ProofCBinaryExpr(op, left, right) => this.pp
        case ProofCUnaryExpr(op, e) => this.pp
      }

    }

    case class ProofCCardinalityConstructor(pred_type: String, name: String, args: List[ProofCExpr]) extends ProofCExpr {
      override def pp: String = s"(${name} ${args.map(_.pp).mkString(" ")} : ${pred_type})"
    }


    /** a variable in a VST proof */
    case class ProofCVar(name: String, typ: VSTProofType) extends ProofCExpr {
      override def pp: String = typ match {
        case ProofTypes.CoqPtrType => name
        case ProofTypes.CoqIntType => name
        case ProofTypes.CoqCardType(_) => name
        case ProofTypes.CoqParamType(ty) =>
          // if the variable has a param type then
          // its actually of type val, and we need to
          // extract it's contained value
          ty match {
            case CTypes.CIntType => s"(${name})"
            case CTypes.CVoidPtrType => s"${name}"
            case CTypes.CUnitType => throw new TranslationException("Error: inconsistent assumptions, attempting to create a variable of unit type")
          }
        case ProofTypes.CoqListType(elem, _) => name
      }
    }

    /** boolean constant in a VST proof */
    case class ProofCBoolConst(value: Boolean) extends ProofCExpr {
      override def pp: String = value.toString
    }

    /** integer constant in a VST proof */
    case class ProofCIntConst(value: Int, is_ptr: Boolean) extends ProofCExpr {
      override def pp: String = if (is_ptr && value == 0) {
        "nullval"
      } else {
        value.toString
      }
    }

    /** set literal (encoded as set) in a VST proof */
    case class ProofCSetLiteral(elems: List[ProofCExpr]) extends ProofCExpr {
      override def pp: String =
        s"[${elems.map(_.pp_as_c_value).mkString("; ")}]"
    }

    /** encodes a ternary expression in a VST proof */
    case class ProofCIfThenElse(cond: ProofCExpr, left: ProofCExpr, right: ProofCExpr) extends ProofCExpr {
      override def pp: String = s"(if ${cond.pp_as_bool_value} then ${left.pp} else ${right.pp})"

      // TODO: if statements don't seem to be used inside suslik proofs, so implementing this would be pointless
      // if this assumption changes, then the correct implementation will look something like:
      //
      //        s"(if ${cond.pp_as_bool_value} then ${left.pp} else ${right.pp})"
      //
      // where pp_as_bool_value should be a method that prints expressions in boolean form
    }

    case class ProofCBinaryExpr(op: ProofCBinOp, left: ProofCExpr, right: ProofCExpr) extends ProofCExpr {
      override def pp: String =
        op match {
          case ProofCOpLt => s"(${left.pp_as_int_value} < ${right.pp_as_int_value})"
          case ProofCOpLeq => s"(${left.pp_as_int_value} <= ${right.pp_as_int_value})"
          case ProofCOpOr => s"(${left.pp} \/ ${right.pp})"
          case ProofCOpAnd => s"(${left.pp} /\ ${right.pp})"
          case ProofCOpPlus => s"(${left.pp} + ${right.pp})"
          case ProofCOpMinus => s"(${left.pp} - ${right.pp})"
          case ProofCOpMultiply => s"(${left.pp} * ${right.pp})"
          case ProofCOpIntEq => s"(${left.pp} = ${right.pp})"
          case ProofCOpBoolEq => s"(${left.pp} = ${right.pp})"
          case ProofCOpPtrEq => s"(${left.pp_as_ptr_value} = ${right.pp_as_ptr_value})"
          case ProofCOpSetEq => s"(${left.pp} = ${right.pp})"
          case ProofCOpUnion => s"(${left.pp} ++ ${right.pp})"
          // case ProofCOpSetEq => s"(eqb_list _ ${left.pp} ${right.pp})"
        }
    }

    case class ProofCUnaryExpr(op: ProofCUnOp, e: ProofCExpr) extends ProofCExpr {
      override def pp: String =
        op match {
          case ProofCOpNot => s"(~ ${e.pp})"
          case ProofCOpUnaryMinus => s"(-(${e.pp}))"
        }
    }

    sealed abstract class ProofCUnOp

    object ProofCOpNot extends ProofCUnOp

    object ProofCOpUnaryMinus extends ProofCUnOp

    sealed abstract class ProofCBinOp

    object ProofCOpImplication extends ProofCBinOp

    object ProofCOpPlus extends ProofCBinOp

    object ProofCOpMinus extends ProofCBinOp

    object ProofCOpMultiply extends ProofCBinOp

    object ProofCOpIntEq extends ProofCBinOp

    object ProofCOpBoolEq extends ProofCBinOp

    object ProofCOpSetEq extends ProofCBinOp

    object ProofCOpPtrEq extends ProofCBinOp

    object ProofCOpLeq extends ProofCBinOp

    object ProofCOpLt extends ProofCBinOp

    object ProofCOpAnd extends ProofCBinOp

    object ProofCOpOr extends ProofCBinOp

    object ProofCOpIn extends ProofCBinOp

    object ProofCOpSubset extends ProofCBinOp

    object ProofCOpUnion extends ProofCBinOp

    object ProofCOpDiff extends ProofCBinOp

    object ProofCOpIntersect extends ProofCBinOp

  }

  /** prop predicate encoding that a given propositional expression is true
    **/
  case class IsTrueProp(expr: Expressions.ProofCExpr) extends PureFormula {
    override def pp: String = {
      s"${expr.pp_as_c_value}"
    }
  }

  /** prop predicate encoding that a given boolean expression is true */
  case class IsTrue(expr: Expressions.ProofCExpr) extends PureFormula {
    override def pp: String = {
      s"(is_true ${expr.pp})"
    }
  }


  sealed case class FormalCondition(
                                     pure_constraints: List[PureFormula],
                                     spatial_constraints: List[VSTHeaplet]
                                   )

  /**
    * Type encoding VST-compliant formal specifications of a C Function
    *
    * @param name               name of the function
    * @param c_params           parameters of the function
    * @param formal_params      parameters of the specification
    * @param existensial_params existential params of the function
    * @param precondition       precondtion for the function
    * @param postcondition      post condition of the function
    * @param return_type        return type of the function
    */
  case class FormalSpecification(
                                  name: Ident,
                                  c_params: Seq[(Ident, VSTCType)],
                                  formal_params: Seq[(Ident, VSTProofType)],
                                  existensial_params: Seq[(Ident, VSTProofType)],
                                  precondition: FormalCondition,
                                  postcondition: FormalCondition,
                                  return_type: VSTCType
                                ) extends PrettyPrinting {

    def as_vst_type(var_type: VSTCType) = var_type match {
      case CTypes.CIntType => "tint"
      case CTypes.CUnitType => "tvoid"
      case CTypes.CVoidPtrType => "(tptr (Tunion _sslval noattr))"
    }

    def params: List[(Ident, VSTProofType)] =
      (c_params.map({ case (name, ty) => (name, CoqParamType(ty)) }) ++ formal_params).toList

    override def pp: String = {
      val formal_args = formal_params.map({ case (var_name, var_type) => s"${var_name}: ${var_type.pp}" })
      val c_args = c_params.map({ case (var_name, _) => s"${var_name}: val" })
      val FormalCondition(pre_pure_constraints, pre_spatial_constraints) = precondition
      val FormalCondition(post_pure_constraints, post_spatial_constraints) = postcondition
      s"""Definition ${name}_spec :=
         |  DECLARE _${name}
         |   WITH ${(c_args ++ formal_args).mkString(", ")}
         |   PRE [ ${c_params.map({ case (_, var_type) => s"${as_vst_type(var_type)}" }).mkString(", ")} ]
         |   PROP( ${pre_pure_constraints.map(_.pp).mkString("; ")} )
         |   PARAMS(${c_params.map({ case (var_name, _) => var_name }).mkString("; ")})
         |   SEP (${pre_spatial_constraints.map(_.pp).mkString("; ")})
         |   POST[ ${as_vst_type(return_type)} ]${
        existensial_params match {
          case Nil => ""
          case _ =>
            "\n" ++
              existensial_params.map({ case (param_name, param_type) => s"|   EX ${param_name}: ${param_type.pp}," }).mkString("\n")
        }
      }
         |   PROP( ${post_pure_constraints.map(_.pp).mkString("; ")} )
         |   LOCAL()
         |   SEP (${post_spatial_constraints.map(_.pp).mkString("; ")}).
         |""".stripMargin
    }
  }

  /**
    * Abstract constructors mapping cardinality constraints to
    * termination measures in Coq
    */
  sealed abstract class CardConstructor extends PrettyPrinting {
    def constructor_args: List[Ident] =
      this match {
        case CardNull => Nil
        case CardOf(args) => args
      }
  }

  /**
    * Null constructor of 0 cardinality
    */
  case object CardNull extends CardConstructor {}

  /** Cardinality constructor of multiple components
    *
    * @param args the variables produced by unwrwapping this element
    */
  case class CardOf(args: List[Ident]) extends CardConstructor {}

  /**
    * Represents helper lemmas and operations that are required to make VST handle the predicate automatically
    **/
  sealed trait VSTPredicateHelper extends PrettyPrinting

  object VSTPredicateHelper {

    case class ValidPointer(predicate: String, args: List[String], ptr: String) extends VSTPredicateHelper {
      def lemma_name: String = s"${predicate}_${ptr}_valid_pointerP"

      override def pp: String =
        s"Lemma ${lemma_name} ${args.mkString(" ")}: ${predicate} ${args.mkString(" ")} |-- valid_pointer ${ptr}. Proof. Admitted."
    }

    case class HintResolve(lemma_name: String, hint_db: String) extends VSTPredicateHelper {
      override def pp: String =
        s"Hint Resolve ${lemma_name} : ${hint_db}."
    }

    case class LocalFacts(predicate: VSTPredicate) extends VSTPredicateHelper {

      def lemma_name: String = s"${predicate.name}_local_factsP"

      override def pp: String = {

        def constructor_to_equality_term(vl: String, cons: CardConstructor) =
          if (cons.constructor_args.isEmpty) {
            s"${vl} = ${predicate.constructor_name(cons)}"
          } else {
            s"exists ${cons.constructor_args.mkString(" ")}, ${vl} = ${predicate.constructor_name(cons)} ${cons.constructor_args.mkString(" ")}"
          }

        /** Converts a predicate clause into a clause that mutually exclusively matches the clause
          *
          * Note: !!ASSUMPTION!! We assume that the first pure term of the predicate mutually exclusively matches the clause
          **/
        def predicate_to_determininant_term(clause: ProofTerms.VSTPredicateClause): String =
          clause.pure.head.pp_as_ptr_value

        /** *
          * Converts a predicate clause into a corresponding fact.
          *
          * NOTE: !!!ASSUMPTION!!! We assume that the first clause of the vst predicate is mutually exclusive - i.e
          * if the first clause holds, then no other clause can hold.
          */
        def clause_fact(cardConstructor: CardConstructor, predicate: VSTPredicateClause): String =
          s"((${predicate_to_determininant_term(predicate)}) -> (${constructor_to_equality_term(predicate.cardinality_param, cardConstructor)}))"


        s"""Lemma ${lemma_name} ${predicate.formal_params.mkString(" ")} :
           |  ${predicate.name} ${predicate.formal_params.mkString(" ")}|-- !!(${
          (
            predicate.clauses.toList.map({ case (cons, pred) => clause_fact(cons, pred) }) ++
              predicate.params.flatMap({ case (param, ProofTypes.CoqPtrType) => Some(s"(is_pointer_or_null ${param})") case _ => None })
            ).mkString("/\\")
        }). Proof. Admitted.""".stripMargin
      }

    }

  }

  /** represents a clause of the VST predicate,
    *
    * @param pure            are the pure assertions
    * @param spatial         are the spatial assertions
    * @param sub_constructor are the subconstructors
    **/
  case class VSTPredicateClause(pure: List[ProofCExpr], spatial: List[VSTHeaplet], sub_constructor: Map[String, CardConstructor]) {

    val cardinality_param: String = "self_card"

    /**
      * @return the selector for the clause
      */
    def selector: ProofCExpr = pure.head

    /** finds existential variables in the expression using args */
    def find_existentials_args(args: Set[String]): List[(Ident, VSTProofType)] = {
      def expr_existential: ProofCExpr => List[(Ident, VSTProofType)] = {
        case Expressions.ProofCVar(name, typ) => if (!args.contains(name)) List((name, typ)) else Nil
        case Expressions.ProofCBoolConst(value) => Nil
        case Expressions.ProofCIntConst(value, _) => Nil
        case Expressions.ProofCSetLiteral(elems) => elems.flatMap(expr_existential)
        case Expressions.ProofCIfThenElse(cond, left, right) => List(cond, left, right).flatMap(expr_existential)
        case Expressions.ProofCBinaryExpr(op, left, right) => List(left, right).flatMap(expr_existential)
        case Expressions.ProofCUnaryExpr(op, e) => expr_existential(e)
      }

      def spatial_expr_existential: VSTHeaplet => List[(Ident, VSTProofType)] = {
        case Formulae.CSApp(pred, args, card) =>
          expr_existential(card) ::: args.flatMap(expr_existential).toList
      }

      pure.flatMap(expr_existential) ++ spatial.flatMap(spatial_expr_existential)
    }

    /** finds existential variables in the expression using args */
    def find_existentials(existentials: Map[Ident, VSTProofType]): List[(Ident, VSTProofType)] = {
      def expr_existential: ProofCExpr => List[(Ident, VSTProofType)] = {
        case Expressions.ProofCVar(name, _) => existentials.get(name).map(typ => (name, typ)).toList
        case Expressions.ProofCBoolConst(value) => Nil
        case Expressions.ProofCIntConst(value, _) => Nil
        case Expressions.ProofCSetLiteral(elems) => elems.flatMap(expr_existential)
        case Expressions.ProofCIfThenElse(cond, left, right) => List(cond, left, right).flatMap(expr_existential)
        case Expressions.ProofCBinaryExpr(op, left, right) => List(left, right).flatMap(expr_existential)
        case Expressions.ProofCUnaryExpr(op, e) => expr_existential(e)
      }

      def spatial_expr_existential: VSTHeaplet => List[(Ident, VSTProofType)] = {
        case Formulae.CSApp(pred, args, card) =>
          expr_existential(card) ::: args.flatMap(expr_existential).toList
        case Formulae.CDataAt(loc, elem_typ, count, elem) =>
          (expr_existential(loc) ++ expr_existential(elem))
      }

      pure.flatMap(expr_existential) ++ spatial.flatMap(spatial_expr_existential)
    }

  }

  /**
    * represents a VST inductive predicate defined in a format that satisfies Coq's termination checker
    *
    * The idea is to conver the cardinality constraints produced by suslik into an inductive datatype
    * with the expectation that each clause of the suslik predicate maps to a unique constructor
    *
    * Constructors are identified by their cardinality, and each suslik predicate maps to a unique cardinality datatype
    *
    * @param name    is the name of the predicate
    * @param params  is the list of arguments to the predicate
    * @param clauses is the mapping from cardinality constructors to clauses
    **/
  case class VSTPredicate(
                           name: Ident, params: List[(String, VSTProofType)],
                           existentials: List[(String, VSTProofType)],
                           clauses: Map[CardConstructor, VSTPredicateClause])
    extends PrettyPrinting {

    /**
      * Returns the constructor of the predicate with n arguments
      *
      * @param n number of arguments
      */
    def constructor_by_arg(n: Int): CardConstructor =
      clauses.find({ case (constructor, clause) => constructor.constructor_args.length == n }).get._1


    /**
      * @param selector a expression corresponding to a selector of the predicate
      * @return cardinality and clause matched by predicate
      */
    def apply(selector: ProofCExpr): (CardConstructor, VSTPredicateClause) =
      clauses.find({ case (_, clause) => clause.selector.equals(selector) }).get


    /** returns any helper lemmas that need to be constructed for the helper */
    def get_helpers: List[VSTPredicateHelper] =
      params.flatMap({
        case (param, ProofTypes.CoqPtrType) =>
          val valid_lemma = VSTPredicateHelper.ValidPointer(name, this.formal_params, param)
          val local_facts = VSTPredicateHelper.LocalFacts(this)
          List(
            valid_lemma, VSTPredicateHelper.HintResolve(valid_lemma.lemma_name, "valid_pointer"),
            local_facts, VSTPredicateHelper.HintResolve(local_facts.lemma_name, "saturate_local")
          )
        case _ => List()
      })


    /** returns the existential variables introduced by a constructor invokation */
    def constructor_existentials(constructor: CardConstructor): List[(Ident, VSTProofType)] = {
      val param_map = params.toMap
      val existential_map = existentials.toMap.filterKeys(key => !param_map.contains(key))
      val predicate = clauses(constructor)
      // clauses(constructor).find_existentials(existential_map)
      find_existentials(constructor)(predicate)
    }

    /** returns all instances of constructors and the bindings they expose */
    def constructors: List[CardConstructor] =
      clauses.flatMap({ case (constructor, VSTPredicateClause(_, _, sub_constructor)) =>
        constructor :: sub_constructor.toList.map({ case (_, constructor) => constructor })
      }).toList

    /** returns all the constructors used in the base match, assumed to be a superset
      * of the constructors used elsewhere
      *
      * Note: to see how there might be constructors elsewhere, suppose we had a cardinality
      * constraint of the form:
      *
      * - `a < self_card`
      *
      * - `b < a`
      *
      * Then the corresponding match case would look like:
      *
      * `pred_1 ((pred_1 b) as a) => ... `
      *
      * I don't this this actually happens in practice, so this is probably just a bit of
      * over-engineering
      **/
    def base_constructors: List[CardConstructor] =
      clauses.map({ case (constructor, _) =>
        constructor
      }).toList

    /**
      * For a given clause of the predicate and its associated constructor,
      * return the list of existential variables used in the body of the clause
      *
      * @param cons    a constructor matching some clause of the predicate
      * @param pclause the corresponding clause of the predicate
      * @return the list of pairs of (variable, variable_type) of all the existential variables in this clause
      **/
    def find_existentials(cons: CardConstructor)(pclause: VSTPredicateClause): List[(String, VSTProofType)] = {
      val param_map = params.toMap
      val exist_map: Map[String, VSTProofType] = existentials.toMap
      val card_map = cons.constructor_args
      pclause match {
        case VSTPredicateClause(pure, spatial, sub_clauses) =>
          val clause_card_map = (card_map ++ sub_clauses.flatMap({ case (_, cons) => cons.constructor_args })).toSet

          def to_variables(exp: ProofCExpr): List[String] = exp match {
            case Expressions.ProofCVar(name, typ) =>
              param_map.get(name) match {
                case None if !clause_card_map.contains(name) => List(name)
                case _ => List()
              }
            case Expressions.ProofCSetLiteral(elems) => elems.flatMap(to_variables)
            case Expressions.ProofCIfThenElse(cond, left, right) =>
              to_variables(cond) ++ to_variables(left) ++ to_variables(right)
            case Expressions.ProofCBinaryExpr(op, left, right) =>
              to_variables(left) ++ to_variables(right)
            case Expressions.ProofCUnaryExpr(op, e) =>
              to_variables(e)
            case _ => List()
          }

          def to_variables_heap(heap: VSTHeaplet): List[String] = heap match {
            case Formulae.CDataAt(loc, elem_typ, count, elem) =>
              to_variables(loc) ++ to_variables(elem)
            case Formulae.CSApp(pred, args, card) =>
              args.flatMap(to_variables).toList
          }

          (pure.flatMap(to_variables) ++ spatial.flatMap(to_variables_heap): List[String])
            .toSet
            .map((v: String) => (v, exist_map(v))).toList
      }
    }

    /** returns the name of the associated cardinality datatype
      * for this predicate */
    def inductive_name: String = s"${name}_card"

    /** Given a cardinality constructor, return the Coq name of the
      * associated cardinality constructor */
    def constructor_name(constructor: CardConstructor): String = {
      val count = constructor match {
        case CardNull => 0
        case CardOf(args) => args.length
      }
      s"${inductive_name}_${count}"
    }

    /** formal parameters of the predicate.
      * This is the sequence of identifiers that will need to be passed to the predicate to instantiate it.  */
    def formal_params: List[String] = params.map({ case (a, _) => a }) ++ List("self_card")

    /** pretty print the constructor  */
    override def pp: String = {
      val constructor_map = base_constructors.map({
        case CardNull => (0, CardNull)
        case v@CardOf(args) => (args.length, v)
      }).toMap

      def pp_constructor(constructor: CardConstructor) = {
        constructor match {
          case CardNull => s"${constructor_name(constructor)} : ${inductive_name}"
          case CardOf(args) =>
            s"${constructor_name(constructor)} : ${(args ++ List(inductive_name)).map(_ => inductive_name).mkString(" -> ")}"
        }
      }

      val inductive_definition = {
        s"""Inductive ${inductive_name} : Set :=
           ${
          constructor_map.map({ case (_, constructor) =>
            s"|    | ${pp_constructor(constructor)}"
          }).mkString("\n")
        }.
           |
           |""".stripMargin
      }

      // This function expands the arguments of a constructor and
      // creates recursive pattern matches if necassary - i.e
      //
      // S ((S b) as a) => .....
      def expand_args(sub_constructor: Map[String, CardConstructor])(idents: List[Ident]): String = {
        idents.map(arg =>
          sub_constructor.get(arg) match {
            case Some(constructor) =>
              s"(${constructor_name(constructor)} ${expand_args(sub_constructor)(constructor.constructor_args)} as ${arg})"
            case None => arg
          }
        ).mkString(" ")
      }

      val predicate_definition =
        s"""Fixpoint ${name} ${params.map({ case (name, proofType) => s"(${name}: ${proofType.pp})" }).mkString(" ")} (self_card: ${inductive_name}) : mpred := match self_card with
           ${
          clauses.map({ case (constructor, pclause@VSTPredicateClause(pure, spatial, sub_constructor)) =>
            s"|    | ${constructor_name(constructor)} ${
              expand_args(sub_constructor)(constructor.constructor_args)
            } => ${
              val clause_existentials: List[(String, VSTProofType)] = find_existentials(constructor)(pclause)
              val str = clause_existentials.map({ case (name, ty) => s"|      EX ${name} : ${ty.pp}," }).mkString("\n")
              clause_existentials match {
                case Nil => ""
                case ::(_, _) => "\n" + str + "\n"
              }
            } ${
              (pure.map(v => s"!!${v.pp}")
                ++
                List((spatial match {
                  case Nil => List("emp")
                  case v => v.map(_.pp)
                }).mkString(" * "))).mkString(" && ")
            }"
          }).mkString("\n")
        }
           |end.
           |""".stripMargin
      s"${inductive_definition}${predicate_definition}"
    }
  }


}


