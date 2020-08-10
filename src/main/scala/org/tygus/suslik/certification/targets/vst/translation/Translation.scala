package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.language.{Expressions, PrettyPrinting, Types}
import org.tygus.suslik.certification.targets.vst.language.Expressions.{CBinOp, CBinaryExpr, CBoolConst, CExpr, CIfThenElse, CNatConst, COpAnd, COpBoolEq, COpDiff, COpEq, COpImplication, COpIn, COpIntersect, COpLeq, COpLt, COpMinus, COpMultiply, COpNot, COpOr, COpPlus, COpSetEq, COpSubset, COpUnaryMinus, COpUnion, CSetLiteral, CUnOp, CUnaryExpr, CVar}
import org.tygus.suslik.certification.targets.vst.language.Types.{AnalysisVSTTypes, CBoolType, CIntType, CUnitType, CVoidPtrPtrType, CVoidPtrType, PtrType, PureType, VSTType}
import org.tygus.suslik.certification.targets.vst.logic.Proof.Proof
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CFunSpec, CInductivePredicate}
import org.tygus.suslik.certification.targets.vst.program.Statements.{CCall, CError, CFree, CGuarded, CHole, CIf, CLoad, CMalloc, CProcedureDefinition, CSeqComp, CSkip, CStatement, CStore}
import org.tygus.suslik.language.Expressions.{BinOp, BinaryExpr, BoolConst, Expr, IfThenElse, IntConst, OpAnd, OpBoolEq, OpDiff, OpEq, OpGeq, OpGt, OpImplication, OpIn, OpIntersect, OpLeq, OpLt, OpMinus, OpMultiply, OpNot, OpNotEqual, OpOr, OpOverloadedEq, OpOverloadedLeq, OpOverloadedMinus, OpOverloadedPlus, OpOverloadedStar, OpPlus, OpSetEq, OpSubset, OpUnaryMinus, OpUnion, OverloadedBinOp, OverloadedBinaryExpr, SetLiteral, UnOp, UnaryExpr, Var}
import org.tygus.suslik.language.{BoolType, CardType, Expressions, Ident, IntType, LocType, SSLType, Statements, VoidType}
import org.tygus.suslik.language.Statements.{Procedure, Statement}
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic.{Environment, FunSpec, InductiveClause, InductivePredicate, PFormula, PredicateEnv, SFormula}

import scala.collection.immutable

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)


  def pp_tuple(value: (PrettyPrinting, PrettyPrinting)) =
    value match {case (v1:PrettyPrinting,v2:PrettyPrinting) => s"${v1.pp} :-> ${v2.pp}"}

  def translate_unary_op(op: UnOp) = op match {
    case OpNot => COpNot
    case OpUnaryMinus => COpUnaryMinus
  }

  def translate_unary_expr(e1: UnaryExpr): CExpr =
    CUnaryExpr(translate_unary_op(e1.op), translate_expression(e1.arg))


  /** translates a variable to C Expression type */
  def translate_variable(param_name: Var) = param_name match {
    case Var(name) => CVar(name)
  }

  def translate_binary_op(op: BinOp): CBinOp = op match {
    case OpImplication => COpImplication
    case OpPlus => COpPlus
    case OpMinus => COpMinus
    case OpMultiply => COpMultiply
    case OpEq => COpEq
    case OpBoolEq => COpBoolEq
    case OpLeq => COpLeq
    case OpLt => COpLt
    case OpAnd => COpAnd
    case OpOr => COpOr
    case OpUnion => COpUnion
    case OpDiff => COpDiff
    case OpIn => COpIn
    case OpSetEq => COpSetEq
    case OpSubset => COpSubset
    case OpIntersect => COpIntersect
  }

  def translate_binary_expr(op: BinOp, e1: Expr, e2: Expr): CExpr = {
    CBinaryExpr(translate_binary_op(op), translate_expression(e1), translate_expression(e2))
  }


  def translate_overloaded_binary_expr(expr: OverloadedBinaryExpr): CExpr = expr match {
    case OverloadedBinaryExpr(overloaded_op, left, right) =>
    val tleft = translate_expression(left)
      val tright = translate_expression(right)
      overloaded_op match {
        case op: BinOp => CBinaryExpr(translate_binary_op(op), tleft, tright)
        case OpOverloadedEq => CBinaryExpr(COpEq, tleft, tright)
        case OpNotEqual =>
          CUnaryExpr(COpNot, CBinaryExpr(COpEq, tleft, tright))
        case OpGt =>
          CUnaryExpr(COpNot, CBinaryExpr(COpLeq, tleft, tright))
        case OpGeq =>
          CUnaryExpr(COpNot, CBinaryExpr(COpLt, tleft, tright))
        case OpOverloadedPlus =>
          CBinaryExpr(COpPlus, tleft, tright)
        case OpOverloadedMinus =>
          CBinaryExpr(COpMinus, tleft, tright)
        case OpOverloadedLeq =>
          CBinaryExpr(COpLeq, tleft, tright)
        case OpOverloadedStar => ???
      }
  }

  /** translate a Suslik expression into VST specific encoding */
  def translate_expression(expr: Expr): CExpr = expr match {
    case Var(name) => CVar(name)
    case BoolConst(value) => CBoolConst(value)
    case IntConst(value) => CNatConst(value)
    case e1@UnaryExpr(_, _) => translate_unary_expr(e1)
    case BinaryExpr(op, e1, e2) => translate_binary_expr(op, e1, e2)
    case SetLiteral(elems) => CSetLiteral(elems.map(e => translate_expression(e)))
    case IfThenElse(c, t, e) => CIfThenElse(translate_expression(c), translate_expression(t), translate_expression(e))
    case expr@OverloadedBinaryExpr(_, _, _) =>
      translate_overloaded_binary_expr(expr)
    case v => throw TranslationException(s"Operation ${v.toString} not supported")
  }


  /** translate type to C Type */
  def translate_type(lType: SSLType): VSTType = {
    lType match {
      case IntType => CIntType
      case BoolType => CBoolType
      case LocType => CVoidPtrType
      case VoidType => CUnitType
      case v => throw TranslationException(s"translating ${v} not implemeneted")
    }

  }

  def translate_clause(clause: InductiveClause) = clause match {
    case InductiveClause(selector: Expr, asn@Assertion(phi: PFormula, sigma: SFormula)) => {
      val c_selector = translate_expression(selector)

      ???
    }
  }

  def translate_predicate(predicate: InductivePredicate) = predicate match {
    case (predicate@InductivePredicate(predicate_name, predicate_params, predicate_clauses: Seq[InductiveClause])) =>
      val params = predicate_params map { case (raw_variable, ty) =>
        val variable = translate_variable(raw_variable)
        val tty = translate_type(ty)
        val clauses = predicate_clauses map translate_clause
        (variable, tty)
      }

      val clauses = predicate_clauses map { case InductiveClause(
      selector: Expr, asn@Assertion(phi: PFormula, sigma: SFormula)
      ) =>
        ???
      }
      (predicate_name, params, clauses)
  }


  def print_as_c_program(f: FunSpec, body: CStatement, ctx: Map[CVar, AnalysisVSTTypes]): String = {

    val c_prelude ="#include <stddef.h>\n\nextern void free(void *p);\n\n"

    val return_type = translate_type(f.rType)
    val body_string = body.ppIndent(1)
    val function_def =
      s"${c_prelude}${return_type.pp} ${f.name}(${
        f.params.map({case (variable_name, _) =>
          s"${ctx(translate_variable(variable_name)).downcast.pp} ${translate_variable(variable_name).pp}"
        }).mkString(", ")
      }) {\n${body_string}\n}\n"
    function_def
  }
  def translate_procedure(f: FunSpec, body: CStatement, ctx: Map[CVar, AnalysisVSTTypes]):
  CProcedureDefinition  = {
    val rt = translate_type(f.rType)
    val params = f.params.map({case (variable_name, _) =>
        (translate_variable(variable_name), ctx(translate_variable(variable_name)).downcast)
      })
    val name = f.name
    CProcedureDefinition(name, rt, params, body)
  }


  def translate(root: CertTree.Node, proc: Procedure, env: Environment):
  (Map[String, CInductivePredicate], CFunSpec, Proof, CProcedureDefinition) = {
    // translate body into VST types, and build context of variables
    var (body, ctx) = translate_body(proc.f, proc.body)
    // use this to build a C-encoding of the synthesized function
    val function_definition = translate_procedure(proc.f, body, ctx)

    // translate predicate to C format


    var body_string = print_as_c_program(proc.f, body, ctx)

    print(body_string)


    // translate predicates
    // translate proof
    ???
  }

  def translate_body(funspec: FunSpec, stmt: Statement) = {
    // build an initial context from the parameters
    var context = funspec.params.map({
      case (variable, ssl_type) => (translate_variable(variable), translate_type(ssl_type).asInstanceOf[AnalysisVSTTypes])
    }).toMap

    // returns the most precise type of the two provided types
    def unify(ty1: AnalysisVSTTypes, ty2: AnalysisVSTTypes): AnalysisVSTTypes = (ty1, ty2) match {
      case (_, CUnitType) => CUnitType
      case (CUnitType, _) => CUnitType
      case (_, CBoolType) => CBoolType
      case (CBoolType, _) => CBoolType
      case (_, CIntType) => CIntType
      case (CIntType, _) => CIntType
      case (ot, CVoidPtrType) => ot
      case (CVoidPtrType, ot) => ot
      case (CVoidPtrPtrType, ot:PtrType) => ot
      case (ot:PtrType, CVoidPtrPtrType) => ot
      case (v1, v2) =>
        if (v1 == v2)
          v1
        else
          throw TranslationException(s"Can not unify type (${v1.pp}) with (${v2.pp})")
    }

    // retrieves the VST Type of the current expression
    def type_expression(expr: CExpr): AnalysisVSTTypes = expr match {
      case value@CVar(_) => context(value)
      case CBoolConst(value) => CBoolType
      case CNatConst(value) => CIntType
      case CIfThenElse(cond, left, right) =>
        val left_ty = type_expression(left)
        val right_ty = type_expression(right)
        unify(left_ty, right_ty)
      case CBinaryExpr(op, left, right) =>
        op match {
          case COpImplication => CBoolType
          case COpPlus => CIntType
          case COpMinus => CIntType
          case COpMultiply => CIntType
          case COpEq => CBoolType
          case COpBoolEq => CBoolType
          case COpLeq => CBoolType
          case COpLt => CBoolType
          case COpAnd => CBoolType
          case COpOr => CBoolType
          case COpIn => CBoolType
          case _ => throw TranslationException("unsupported binary operand in function body")
        }
      case CUnaryExpr(op, e) => op match {
        case COpNot => CBoolType
        case COpUnaryMinus => CIntType
      }
      case CSetLiteral(elems) => throw TranslationException("unsupported expression in function body")
    }

    def debug() = {
      print("context = {\n"+context.map({case (variable, ty) => s"\t${variable.pp}: ${ty.pp}\n"}) + "}\n")
    }
    // a very light abstract interpretation of the suslik program to convert types to
    // C-like types
    // should reach fixpoint in two iterations
    def eval_statement(stmt: Statement): Unit =
      stmt match {
          // T to = malloc(sz * sizeof(tpe));
        case Statements.Malloc(to, tpe, sz) =>
          val to_variable = translate_variable(to)
          val old_ty = context.getOrElse(to_variable, CVoidPtrType)
          context = context.updated(to_variable, unify(old_ty, translate_type(tpe)))
          // println(s"after Malloc(${to.pp}, ${tpe.pp}, ${sz.toString})")
          // debug()

          // T to = *(from + offset);
        case Statements.Load(to, _, from, offset) =>
          val to_variable = translate_variable(to)
          val from_variable = translate_variable(from)

          // use the type of variable being stored into to infer type of the from variable
          context.get(to_variable) match {
            case Some(value : PureType) =>
              val from_type = Types.ptr_type(value)
              val old_from_type = context.getOrElse(from_variable, from_type)
              context = context.updated(from_variable, unify(from_type, old_from_type))
            case _ => ()
          }
          // use the type of the variable being stored to infer type of the variable being stored into
          context.get(from_variable) match {
            case Some(value : PtrType) =>
              val to_type = Types.deref_type(value)
              val old_to_type = context.getOrElse(to_variable, to_type)
              context = context.updated(to_variable, unify(to_type, old_to_type))
            case Some(CVoidPtrType) =>
              /* in this case, we're de-referencing a void pointer, which is clearly
              * impossible - hence we'll state that from_variable is a void ** type and to
              * is void * type  */
              context = context.updated(from_variable, CVoidPtrPtrType)
              context = context.updated(to_variable, CVoidPtrType)
            case _ => ()
          }
        case Statements.Store(to, offset, e) =>
          // when storing, we can be assured that the
          // type of the to element must be *(type of assignment expression)
          val to_variable = translate_variable(to)
          // type of expression being assigned
          val expr = translate_expression(e)
          val expr_ty = type_expression(expr)

          // we expect the type of the storage location to be
          // a pointer to elements of the type of the stored
          // expression
          expr_ty match {
            case pureType: PureType =>
              val to_type  = Types.ptr_type(pureType)
              // retrieve the old type
              var old_to_type : AnalysisVSTTypes = context.getOrElse(to_variable, to_type)

              // unify the expected type vs the stored type
              context = context.updated(to_variable, unify(to_type,old_to_type))
            case v => ()
          }

          // additional case for the situation in which our expression is just another pointer
          // i.e *to = from
          // then we can use properties about to to infer the type of from
          expr match {
            case from_variable@CVar(_) =>
              context.get(to_variable) match {
                case Some (ptrType: PtrType) =>
                  val from_type = Types.deref_type(ptrType)
                  var old_from_type : AnalysisVSTTypes = context.getOrElse(from_variable, from_type)
                  context = context.updated(from_variable, unify(from_type,old_from_type))
              }
            case _ => ()
          }
        case Statements.SeqComp(s1, s2) =>
          eval_statement(s1)
          eval_statement(s2)
        case Statements.If(cond, tb, eb) =>
          cond match {
            case variable@Var(_) => context = context.updated(translate_variable(variable), CBoolType)
            case _ => ()
          }
          eval_statement(tb)
          eval_statement(eb)
        case Statements.Guarded(cond, body, els, branchPoint) =>
          cond match {
            case variable@Var(_) => context = context.updated(translate_variable(variable), CBoolType)
            case _ => ()
          }
          eval_statement(body)
          eval_statement(els)
        // case Statements.Call(fun, args, companion) => () // TODO: Should probably also handle this, but for now it works

        // everything else, we ignore
        case _ => ()
      }

    // assuming a completed context, converts suslik statement to VST C statements
    def translate_statement(stmt: Statement): CStatement =
      stmt match {
        case Statements.Skip => CSkip
        case Statements.Hole => CHole
        case Statements.Error => CError
        case Statements.Malloc(to, _, sz) =>
          CMalloc(translate_variable(to), context(translate_variable(to)).downcast, sz)
        case Statements.Free(v) =>
          CFree(translate_variable(v))
        case Statements.Load(to, _, from, offset) =>
          val to_var = translate_variable(to)
          val from_var = translate_variable(from)
          CLoad(to_var,  context(to_var).downcast, from_var, offset)
        case Statements.Store(to, offset, e) =>
          val to_variable = translate_variable(to)
          val expr = translate_expression(e)
          CStore(to_variable, type_expression(expr).downcast, offset, expr)
        case Statements.Call(fun, args, companion) =>
          CCall(translate_variable(fun), args map translate_expression, companion)
        case Statements.SeqComp(s1, s2) =>
          CSeqComp(translate_statement(s1), translate_statement(s2))
        case Statements.If(cond, tb, eb) =>
          CIf(translate_expression(cond), translate_statement(tb), translate_statement(eb))
        case Statements.Guarded(cond, body, els, branchPoint) =>
          CGuarded(translate_expression(cond), translate_statement(body), translate_statement(els), branchPoint)
      }

    // first, run program analysis
    var prev_context = context
    do {
      prev_context = context
      eval_statement(stmt)
    } while (prev_context != context)

    // then translate the body
    val body: CStatement = translate_statement(stmt)

    // QED
    (body, context)
  }

}
