package org.tygus.suslik.logic.smt

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.interpreters.{Resources, SMTSolver}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax._
import org.bitbucket.franck44.scalasmt.theories._
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, QuantifiedTerm, TypedTerm, VarTerm}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{IntSetType, IntType, BoolType, LocType}
import org.tygus.suslik.logic._

import scala.util.Success

/**
  * @author Ilya Sergey
  */

object SMTSolving extends Core
  with IntegerArithmetics
  with QuantifiedTerm
  with Resources
  with Commands
  with PureLogicUtils
  with ArrayExBool
  with ArrayExOperators {

//  val defaultSolver = "CVC4"
  val defaultSolver = "Z3"

  implicit private var solverObject: SMTSolver = null

  {
    disableLogging()

    // create solver and assert axioms
    // TODO: destroy solver when we're done
    solverObject = new SMTSolver(defaultSolver, new SMTInit())
    for (cmd <- prelude) { solverObject.eval(Raw(cmd)) }

  }

  /** Communication with the solver  */

  trait SetTerm

  type SMTBoolTerm = TypedTerm[BoolTerm, Term]
  type SMTIntTerm = TypedTerm[IntTerm, Term]
  //  type SMTSetTerm = TypedTerm[ArrayTerm[BoolTerm], Term]
  type SMTSetTerm = TypedTerm[SetTerm, Term]

  def setSort: Sort = SortId(SymbolId(SSymbol("SetInt")))
  def emptySetSymbol = SimpleQId(SymbolId(SSymbol("empty")))
  def setInsertSymbol = SimpleQId(SymbolId(SSymbol("insert")))
  def setUnionSymbol = SimpleQId(SymbolId(SSymbol("union")))
  def setDiffSymbol = SimpleQId(SymbolId(SSymbol("difference")))
  def setMemberSymbol = SimpleQId(SymbolId(SSymbol("member")))
  def setSubsetSymbol = SimpleQId(SymbolId(SSymbol("subset")))
  def emptySetTerm: Term = QIdTerm(emptySetSymbol)

  // Commands to be executed before solving starts
  def prelude = if (defaultSolver == "CVC4") {
    List(
      "(set-logic ALL_SUPPORTED)",
      "(define-sort SetInt () (Set Int))",
      "(define-fun empty () SetInt (as emptyset (Set Int)))")
  } else if (defaultSolver == "Z3") {
    List(
      "(define-sort SetInt () (Array Int Bool))",
      "(define-fun empty () SetInt ((as const SetInt) false))",
      "(define-fun member ((x Int) (s SetInt)) Bool (select s x))",
      "(define-fun insert ((x Int) (s SetInt)) SetInt (store s x true))")
//      "(define-fun subset ((s1 SetInt) (s2 SetInt)) Bool (= s1 (intersect s1 s2)))")
//      "(define-fun union ((s1 SetInt) (s2 SetInt)) SetInt (((_ map or) s1 s2)))",
//      "(define-fun andNot ((b1 Bool) (b2 Bool)) Bool (and b1 (not b2)))",
//      "(define-fun diff ((s1 SetInt) (s2 SetInt)) SetInt (((_ map andNot) s1 s2)))")
  } else throw SolverUnsupportedExpr(defaultSolver)

  private def checkSat(term: SMTBoolTerm): Boolean =
    this.synchronized {
      push(1)
      val res = isSat(term)
      pop(1)
      res != Success(UnSat()) // Unknown counts as SAT
    }

  /** Translating expression into SMT  */

  case class SMTUnsupportedExpr(e: Expr)
    extends Exception(s"Cannot convert expression ${e.pp} to an equivalent SMT representation.")

  case class SolverUnsupportedExpr(solver: String)
    extends Exception(s"Unsupported solver: $solver.")

  private def convertFormula(phi: PFormula, gamma: Gamma): SMTBoolTerm = convertBoolExpr(phi, gamma)

  private def convertSetExpr(e: Expr, gamma: Gamma): SMTSetTerm = e match {
    case Var(name) => new VarTerm[ SetTerm ]( name, setSort )
    case SetLiteral(elems) => {
      val emptyTerm = new TypedTerm[SetTerm, Term](Set.empty, emptySetTerm)
      makeSetInsert(emptyTerm, elems, gamma)
    }
    // Special case for unions with a literal
    case BinaryExpr(OpUnion, SetLiteral(elems1), SetLiteral(elems2)) => {
      val emptyTerm = new TypedTerm[SetTerm, Term](Set.empty, emptySetTerm)
      makeSetInsert(emptyTerm, elems1 ++ elems2, gamma)
    }
    case BinaryExpr(OpUnion, left, SetLiteral(elems)) => {
      val l = convertSetExpr(left, gamma)
      makeSetInsert(l, elems, gamma)
    }
    case BinaryExpr(OpUnion, SetLiteral(elems), right) => {
      val r = convertSetExpr(right, gamma)
      makeSetInsert(r, elems, gamma)
    }
    case BinaryExpr(OpUnion, left, right) => {
      val l = convertSetExpr(left, gamma)
      val r = convertSetExpr(right, gamma)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setUnionSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpDiff, left, right) => {
      val l = convertSetExpr(left,gamma)
      val r = convertSetExpr(right, gamma)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setDiffSymbol, List(l.termDef, r.termDef)))
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def makeSetInsert(setTerm: SMTSetTerm, elems: List[Expr], gamma: Gamma): SMTSetTerm = {
    if (elems.isEmpty) {
      setTerm
    } else {
      val eTerms: List[SMTIntTerm] = elems.map(convertIntExpr(_, gamma))
      if (defaultSolver == "CVC4") {
        new TypedTerm[SetTerm, Term](setTerm.typeDefs ++ eTerms.flatMap(_.typeDefs).toSet,
          QIdAndTermsTerm(setInsertSymbol, (eTerms :+ setTerm).map(_.termDef)))
      } else if (defaultSolver == "Z3") {
        def makeInsertOne(setTerm: SMTSetTerm, eTerm: SMTIntTerm): SMTSetTerm =
          new TypedTerm[SetTerm, Term](setTerm.typeDefs ++ eTerm.typeDefs,
            QIdAndTermsTerm(setInsertSymbol, List(eTerm.termDef, setTerm.termDef)))
        eTerms.foldLeft(setTerm)(makeInsertOne)
      } else throw SolverUnsupportedExpr(defaultSolver)
    }
  }

  private def convertBoolExpr(e: Expr, gamma: Gamma): SMTBoolTerm =  e match {
    case Var(name) => Bools(name)
    case BoolConst(true) => True()
    case BoolConst(false) => False()
    case UnaryExpr(OpNot, e1) => !convertBoolExpr(e1, gamma)
    case BinaryExpr(OpAnd, left, right) => {
      val l = convertBoolExpr(left, gamma)
      val r = convertBoolExpr(right, gamma)
      l & r }
    case BinaryExpr(OpOr, left, right) => {
      val l = convertBoolExpr(left, gamma)
      val r = convertBoolExpr(right, gamma)
      l | r }
    case BinaryExpr(OpEq1, left, right) => {
      val l = convertIntExpr(left, gamma)
      val r = convertIntExpr(right, gamma)
      l === r }
    case BinaryExpr(OpOverloadedEq, left, right) =>
      (left.getType(gamma), right.getType(gamma)) match {
        case (Some(IntSetType), Some(IntSetType)) => convertBoolExpr(BinaryExpr(OpSetEq1, left, right), gamma)
        case (Some(IntType), Some(IntType))
             | (Some(LocType), Some(LocType))
             | (Some(IntType), Some(LocType))
             | (Some(LocType), Some(IntType))
        => {
          convertBoolExpr(BinaryExpr(OpEq1, left, right), gamma)
        }
        case other => {
          throw new RuntimeException("unexpected types for `==` operator: " + other)
        }
      }
    case BinaryExpr(OpLeq, left, right) => {
      val l = convertIntExpr(left, gamma)
      val r = convertIntExpr(right, gamma)
      l <= r }
    case BinaryExpr(OpLt, left, right) => {
      val l = convertIntExpr(left, gamma)
      val r = convertIntExpr(right, gamma)
      l < r }
    case BinaryExpr(OpIn, left, right) => {
      val l = convertIntExpr(left, gamma)
      val r = convertSetExpr(right, gamma)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(setMemberSymbol, List(l.termDef, r.termDef)))
      }
    case BinaryExpr(OpSetEq1, left, right) => {
      val l = convertSetExpr(left, gamma)
      val r = convertSetExpr(right, gamma)
      l === r }
    case BinaryExpr(OpSubset, left, right) => {
      val l = convertSetExpr(left, gamma)
      val r = convertSetExpr(right, gamma)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(setSubsetSymbol, List(l.termDef, r.termDef)))
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def convertIntExpr(e: Expr, gamma: Gamma): SMTIntTerm = e match {
    case Var(name) => Ints(name)
    case IntConst(c) => Ints(c)
    case BinaryExpr(op, left, right) => {
      val l = convertIntExpr(left, gamma)
      val r = convertIntExpr(right, gamma)
      op match {
        case OpPlus => l + r
        case OpMinus => l - r
        case _ => throw SMTUnsupportedExpr(e)
      }}
    case IfThenElse(cond, left, right) => {
      val c = convertBoolExpr(cond, gamma)
      val l = convertIntExpr(left, gamma)
      val r = convertIntExpr(right, gamma)
      c.ite(l,r) }
    case _ => throw SMTUnsupportedExpr(e)
  }

  /** Caching */

  private val cache = collection.mutable.Map[PFormula, Boolean]()
  def cacheSize: Int = cache.size

  // Call this before synthesizing a new function
  def init(): Unit = {
    // Warm up solver
    cache.clear()
  }

  /** External interface */

  // Check if phi is satisfiable; all vars are implicitly existentially quantified
  def sat(phi: PFormula, gamma: Gamma): Boolean = {
    cache.getOrElseUpdate(phi, checkSat(convertFormula(phi, gamma)))
  }

  // Check if phi is valid; all vars are implicitly universally quantified
  def valid(phi: PFormula, gamma: Gamma): Boolean = {
    !sat(phi.not, gamma)
  }

}
