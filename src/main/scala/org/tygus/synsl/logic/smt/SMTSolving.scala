package org.tygus.synsl.logic.smt

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.configurations.SMTLogics.QF_LIA
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

object SMTSolving extends Core with IntegerArithmetics with ArrayExInt with Resources with Commands
    with PureLogicUtils {

  {
    disableLogging()
    // new SMTSolver("Z3", new SMTInit(QF_LIA, List(MODELS)))
  }

  case class SMTUnsupportedFormula(phi: PFormula)
      extends Exception(s"Cannot convert formula ${phi.pp} to an equivalent SMT representation.")

  case class SMTUnsupportedExpr(e: Expr)
      extends Exception(s"Cannot convert expression ${e.pp} to an equivalent SMT representation.")

  implicit def _phi2Exn(phi: PFormula): Throwable = SMTUnsupportedFormula(phi)
  implicit def _expr2Exn(e: Expr): Throwable = SMTUnsupportedExpr(e)

  type SMTBoolTerm = TypedTerm[BoolTerm, Term]
  type SMTIntTerm = TypedTerm[IntTerm, Term]

  /*
  TODO:
  1. Implement conversion not only for integers based on the type (guess type)
   */

  private def checkImplication(ant: SMTBoolTerm, succ: SMTBoolTerm): Boolean = {
    val conjecture = ant imply succ
    val res = using(new SMTSolver("Z3", new SMTInit(QF_LIA, List(MODELS)))) { implicit solver => isSat(!conjecture) }
    res == Success(UnSat())
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

    case _ => Failure(phi)
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

  // Check phi1 => phi2; all vars assumed to be universally quantified
  def implies(phi1: PFormula, phi2: PFormula): Boolean = {
    // Check satisfiability via SMT
    val res = for {
      p1 <- convertFormula(phi1)
      p2 <- convertFormula(phi2)
    } yield checkImplication(p1, p2)
    res.getOrElse(false)
  }

}
