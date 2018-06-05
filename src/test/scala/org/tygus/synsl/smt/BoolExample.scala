package org.tygus.synsl.smt

/**
  * @author Ilya Sergey
  */

import java.sql.JDBCType

import org.bitbucket.franck44.scalasmt.interpreters.Resources
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax._
import org.bitbucket.franck44.scalasmt.theories.{BoolTerm, Core, IntegerArithmetics}
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, TypedTerm}

import scala.util.Success

object BoolExample extends Core with IntegerArithmetics with Resources with Commands {

  disableLogging()

  import org.bitbucket.franck44.scalasmt.configurations.SMTInit
  import org.bitbucket.franck44.scalasmt.configurations.SMTLogics._
  import org.bitbucket.franck44.scalasmt.configurations.SMTOptions.MODELS
  import org.bitbucket.franck44.scalasmt.interpreters.SMTSolver

  //  create two SMTLIB2 Int variables using the DSL
  val p = Bools("p")
  val q = Bools("q")
  val r = Bools("r")

  /*
  	(=> (and (=> p q) (=> q r))
		(=> p r)))
   */

  val conjecture1: TypedTerm[BoolTerm, Term] = !(((p imply q) & (q imply r)) imply (p imply r))
  val conjecture2: TypedTerm[BoolTerm, Term] = !(p imply p)

  def testConjecture(conj: TypedTerm[BoolTerm, Term]): Unit =  {
    val t1 = System.currentTimeMillis()
    implicit lazy val solver = new SMTSolver("Z3", new SMTInit(QF_LIA, List(MODELS)))
    val res = using(solver) { implicit solver => isSat(conj) }
    val t2 = System.currentTimeMillis()
    println(res)
    println(t2 - t1)
    assert(res == Success(UnSat()))

  }

  def main(args: Array[String]): Unit = {
    testConjecture(conjecture1)
    testConjecture(conjecture2)
    testConjecture(conjecture1)
  }
}