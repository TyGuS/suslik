package org.tygus.synsl.logic.smt

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.configurations.SMTLogics.{QF_AUFLIA, QF_LIA, AUFNIRA}
import org.bitbucket.franck44.scalasmt.configurations.SMTOptions.MODELS
import org.bitbucket.franck44.scalasmt.interpreters.{Resources, SMTSolver}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax._
import org.bitbucket.franck44.scalasmt.theories._
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, QuantifiedTerm, TypedTerm}
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.logic._

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

  // val defaultSolver = "CVC4"
  val defaultSolver = "Z3"
  implicit var solverObject: SMTSolver = null

  {
    disableLogging()

    // create solver and assert axioms
    // TODO: destroy solver when we're done
    solverObject = new SMTSolver(defaultSolver, new SMTInit(AUFNIRA, List(MODELS)))
    |=(emptyDef)
  }

  // Call this before synthesizing a new function
  def init(): Unit = {
    cache.clear()
  }

  case class SMTUnsupportedFormula(phi: PFormula)
      extends Exception(s"Cannot convert formula ${phi.pp} to an equivalent SMT representation.")

  case class SMTUnsupportedExpr(e: Expr)
      extends Exception(s"Cannot convert expression ${e.pp} to an equivalent SMT representation.")

  implicit def _phi2Exn(phi: PFormula): Throwable = SMTUnsupportedFormula(phi)
  implicit def _expr2Exn(e: Expr): Throwable = SMTUnsupportedExpr(e)

  type SMTBoolTerm = TypedTerm[BoolTerm, Term]
  type SMTIntTerm = TypedTerm[IntTerm, Term]
  type SMTSetTerm = TypedTerm[ArrayTerm[BoolTerm], Term]

  private def checkSat(term: SMTBoolTerm): Boolean = {
    push(1)
    val res = isSat(term)
    pop(1)
    res == Success(Sat())
  }

  private def convertFormula(phi: PFormula): SMTBoolTerm = convertBoolExpr(phi.toExpr)

//  private def convertIntSetExpr(e: Expr): Try[(SMTSetTerm, SMTBoolTerm)] = e match {
//    case Var(name) => Try((ArrayBool1(name), True()))
//    case SingletonSet(elem) => Failure(e)
//    //  TODO: support the rest
//    case EmptySet => Failure(e)
//    case SetUnion(l, r) => Failure(e)
//    case _ => Failure(e)
//  }

  private def convertSetExpr(e: Expr): SMTSetTerm = e match {
    case Var(name) => ArrayBool1(name)
    case SetLiteral(elems) => elems.foldLeft(emptySet)((res, elem) => res.store(convertIntExpr(elem), True()))
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def convertBoolExpr(e: Expr): SMTBoolTerm =  e match {
    case Var(name) => Bools(name)
    case BoolConst(true) => True()
    case BoolConst(false) => False()
    case UnaryExpr(OpNot, e1) => !convertBoolExpr(e1)
    case BinaryExpr(OpAnd, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l & r }
    case BinaryExpr(OpOr, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l | r }
    case BinaryExpr(OpEq, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l === r }
    case BinaryExpr(OpLeq, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l <= r }
    case BinaryExpr(OpLt, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l < r }
    case BinaryExpr(OpIn, left, right) => {
      val l = convertIntExpr(left)
      val r = convertSetExpr(right)
      r(l) }
    case BinaryExpr(OpSetEq, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      l === r }
    case _ => throw SMTUnsupportedExpr(e)
  }

    //    case SEq(SingletonSet(s1), SingletonSet(s2)) => for {
    //      l <- convertIntExpr(s1)
    //      r <- convertIntExpr(s2)
    //    } yield l === r
    // TODO: support other cases


  private def convertIntExpr(e: Expr): SMTIntTerm = e match {
    case Var(name) => Ints(name)
    case IntConst(c) => Ints(c)
    case BinaryExpr(op, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      op match {
        case OpPlus => l + r
        case OpMinus => l - r
        case _ => throw SMTUnsupportedExpr(e)
      }}
    case IfThenElse(cond, left, right) => {
      val c = convertBoolExpr(cond)
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      c.ite(l,r) }
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def emptySet: SMTSetTerm = ArrayBool1("empty")
  private def emptyDef: SMTBoolTerm = forall(Ints("x").symbol) {
    val x = Ints("x")
    !emptySet(x)
  }

  private val cache = collection.mutable.Map[PFormula, Boolean]()
  def cacheSize: Int = cache.size

  // Check if phi is satisfiable; all vars are implicitly existentially quantified
  def sat(phi: PFormula): Boolean = {
    cache.getOrElseUpdate(phi, checkSat(convertFormula(phi)))
  }

  // Check if phi is valid; all vars are implicitly universally quantified
  def valid(phi: PFormula): Boolean = {
    !sat(PNeg(phi))
  }

}
