package org.tygus.synsl.logic.smt

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.configurations.SMTLogics.{QF_AUFLIA, QF_LIA}
import org.bitbucket.franck44.scalasmt.configurations.SMTOptions.MODELS
import org.bitbucket.franck44.scalasmt.interpreters.{Resources, SMTSolver}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax._
import org.bitbucket.franck44.scalasmt.theories._
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, TypedTerm}
import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.logic._

import scala.util.{Failure, Success, Try}

/**
  * @author Ilya Sergey
  */

object SMTSolving extends Core with IntegerArithmetics with Resources with Commands
    with PureLogicUtils with ArrayExBool {

  {
    disableLogging()
    // new SMTSolver("Z3", new SMTInit(QF_LIA, List(MODELS)))
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

  /*
  TODO:
  1. Implement conversion not only for integers based on the type (guess type)
   */

  private def checkSat(term: SMTBoolTerm): Boolean = {
    val res = using(new SMTSolver("Z3", new SMTInit(QF_LIA, List(MODELS)))) { implicit solver => isSat(term) }
    res == Success(Sat())
  }


  private def convertFormula(phi: PFormula): Try[SMTBoolTerm] = phi match {
    case PTrue => Try(True())
    case PFalse => Try(False())
    case PNeg(arg) => for {p <- convertFormula(arg)} yield !p
    case PAnd(left, right) => for {
      l <- convertFormula(left)
      r <- convertFormula(right)
    } yield l & r
    case POr(left, right) => for {
      l <- convertFormula(left)
      r <- convertFormula(right)
    } yield l | r

    // General equality
    // TODO: Make sure not only integers are supported!
    case PEq(left, right) => for {
      l <- convertIntExpr(left)
      r <- convertIntExpr(right)
    } yield l === r

    // Arithmetic
    case PLeq(left, right) => for {
      l <- convertIntExpr(left)
      r <- convertIntExpr(right)
    } yield l <= r
    case PLtn(left, right) => for {
      l <- convertIntExpr(left)
      r <- convertIntExpr(right)
    } yield l < r

    case SEq(SingletonSet(s1), SingletonSet(s2)) => for {
      l <- convertIntExpr(s1)
      r <- convertIntExpr(s2)
    } yield l === r
    // TODO: support other cases

    case _ => Failure(phi)
  }

  private def convertIntSetExpr(e: Expr): Try[(SMTSetTerm, SMTBoolTerm)] = e match {
    case Var(name) => Try((ArrayBool1(name), True()))
    case SingletonSet(elem) => Failure(e)
    //  TODO: support the rest
    case EmptySet => Failure(e)
    case SetUnion(l, r) => Failure(e)
    case _ => Failure(e)
  }

  // So far only ints are supported
  private def convertIntExpr(e: Expr): Try[SMTIntTerm] = e match {
    case Var(name) => Try(Ints(name))
    case IntConst(c) => Try(Ints(c))
    case BinaryExpr(op, left, right) => for {
      l <- convertIntExpr(left)
      r <- convertIntExpr(right)
    } yield op match {
      case OpPlus => l + r
      case OpMinus => l - r
      case _ => throw SMTUnsupportedExpr(e)
    }
    case UnaryExpr(op, arg) => Failure(e)
    case _ => Failure(e)
  }

  private val cache = collection.mutable.Map[PFormula, Boolean]()
  def cacheSize: Int = cache.size

  // Check if phi is satisfiable; all vars are implicitly existentially quantified
  def sat(phi: PFormula): Boolean = {
    def check(phi: PFormula): Boolean = {
        val res: Try[Boolean] = for {
          p <- convertFormula(phi)
        } yield checkSat(p)
        res.getOrElse(true)
    }
    cache.getOrElseUpdate(phi, check(phi))
  }

  // Check if phi is valid; all vars are implicitly universally quantified
  def valid(phi: PFormula): Boolean = {
    !sat(PNeg(phi))
  }

}
