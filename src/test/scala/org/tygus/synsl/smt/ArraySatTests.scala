package org.tygus.synsl.smt

/*
 * This file is adopted from ScalaSMT.
 *
 * Copyright (C) 2015-2018 Franck Cassez.
 *
 * ScalaSMT is free software: you can redistribute it and/or modify it un-
 * der the terms of the  GNU Lesser General Public License as published by
 * the Free Software Foundation,  either version 3  of the License, or (at
 * your option) any later version.
 *
 * ScalaSMT is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY;  without  even the implied   warranty  of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with ScalaSMT. (See files COPYING and COPYING.LESSER.) If not, see
 * <http://www.gnu.org/licenses/>.
 */

import org.bitbucket.franck44.scalasmt.interpreters.Resources
import org.bitbucket.franck44.scalasmt.theories._
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, TypedTerm, VarTerm}
import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.{FunSuite, Matchers}
import org.slf4j.LoggerFactory

/**
  * Check sat for array terms
  */
class ArraySatTests
    extends FunSuite
        with TableDrivenPropertyChecks
        with Matchers
        with Core
        with IntegerArithmetics
        with BitVectors
        with ArrayExInt
        with ArrayExBool
        with ArrayExReal
        with ArrayExBV
        with ArrayExOperators
        with Commands
        with Resources {

  import org.slf4j.LoggerFactory

  //  logger
  private val logger = LoggerFactory.getLogger(this.getClass)

  override def suiteName = s"Check sat for simple assertions with arrays"

  import org.bitbucket.franck44.scalasmt.configurations.AppConfig.config
  import org.bitbucket.franck44.scalasmt.configurations.SMTLogics.{QF_ABV, QF_AUFLIA}
  import org.bitbucket.franck44.scalasmt.configurations.{SMTInit, SMTLogics}
  import org.bitbucket.franck44.scalasmt.interpreters.SMTSolver
  import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax.{Sat, SatResponses, Term, UnSat}

  import scala.util.Success

  //  Solvers to be included in the tests
  val theSolvers = Table("Solver", config.filter(_.enabled): _*)

  val a1 = ArrayInt1("a")
  val a1i1 = ArrayInt1("a") indexed 0
  val b1 = ArrayInt1("b")
  val a2 = ArrayInt2("a")
  val a2i9 = ArrayInt2("a") indexed 9
  val bv1 = ArrayBV1("bv1", 2, 4)
  val bv2 = ArrayBV1("bv2", 6, 4)

  //  format: OFF
  val theTerms = Table[String, TypedTerm[BoolTerm, Term], SatResponses, SMTLogics.Value](
    ("expression", "TypedTerm", "Expected status", "logic"),
    ("a[0] == 1", a1(0) === 1, Sat(), QF_AUFLIA),
    ("a_0[0] == 1", a1i1(0) === 1, Sat(), QF_AUFLIA),
    ("a[0] == 1 & a[0] > 2", a1(0) === 1 & a1(0) > 2, UnSat(), QF_AUFLIA),
    ("a[0] == 1 & b[0] > a[0]", a1.at(0) === 1 & a1(0) > 2, UnSat(), QF_AUFLIA),
    ("a[0] == b & b[0] <= 1", a2(0) === b1 & b1(0) <= 2, Sat(), QF_AUFLIA),
    ("a_9[0] == b & b[0] <= 1", a2i9(0) === b1 & b1(0) <= 2, Sat(), QF_AUFLIA),
    ("a[0] == b & b[0] <= 2", a2(0) === b1 & b1(0) <= 2, Sat(), QF_AUFLIA),
    ("bv1[#b01] == #x1 & bv2[#b111111] > bv1[#b00]", bv1.at(BVs(0, 2)) === BVs(1, 4) & (bv1(BVs(1, 2)) ult bv2(BVs(2, 6))), Sat(), QF_ABV),
    ("bv1[#b01] == #x1 & bv1[#b01] > #b01", bv1.at(BVs(0, 2)) === BVs(1, 4) & (bv1(BVs(0, 2)) ult BVs(1, 4)), UnSat(), QF_ABV)

  )
  //  format: ON

  for (s ← theSolvers; (txt, t, r, l) ← theTerms if s.supportedLogics.contains(l)) {
    //  initialise sequence
    val initSeq = new SMTInit(l, List())
    test(s"[${s.name}] configured with ${initSeq.show} to check sat for $txt ") {
      using(new SMTSolver(s, initSeq)) {
        implicit solver ⇒ {
          //  smtlib package eval is used
          isSat(t)
        }
      } shouldBe Success(r)
    }
  }
}

/**
  * Check sat for array terms: if sat get a value for the arrays
  */
class ArrayValueTests
    extends FunSuite
        with TableDrivenPropertyChecks
        with Matchers
        with Core
        with IntegerArithmetics
        with ArrayExInt
        with ArrayExBool
        with ArrayExReal
        with ArrayExOperators
        with Commands
        with Resources {


  override def suiteName = s"Check sat for simple assertions with arrays"

  import org.bitbucket.franck44.scalasmt.configurations.AppConfig.config
  import org.bitbucket.franck44.scalasmt.configurations.SMTInit
  import org.bitbucket.franck44.scalasmt.configurations.SMTLogics.QF_AUFLIA
  import org.bitbucket.franck44.scalasmt.configurations.SMTOptions.MODELS
  import org.bitbucket.franck44.scalasmt.interpreters.SMTSolver
  import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax.{Sat, Term}

  import scala.util.{Failure, Success}

  //  Solvers to be included in the tests
  val theSolvers = Table(
    "Solver",
    config.filter(
      n ⇒ !(n.name contains "nonIncr") && n.enabled &&
          n.supportedLogics.contains(QF_AUFLIA)): _*)
  //  dimension 1 arrays
  val a1 = ArrayInt1("a1")
  val a1i1 = ArrayInt1("a1") indexed 0
  val b1 = ArrayInt1("b1")
  //  dimension 2 arrays
  val a2 = ArrayInt2("a2")
  val b2 = ArrayInt2("b2")
  val a2i9 = ArrayInt2("a2") indexed 9

  //  format: OFF
  val theTerms1 = Table[String, TypedTerm[BoolTerm, Term], List[VarTerm[ArrayTerm[IntTerm]]]](
    ("expression", "TypedTerm", "Values"),
    ("a[0] == 1", a1(0) === 1, List(a1)),
    ("a_0[0] == 1", a1i1(0) === 1, List(a1i1)),
    ("a[0] == b[1] & b[0] <= 1", a1(0) === b1(1) & b1(0) <= 2, List(a1, b1))
  )

  val theTerms2 = Table[String, TypedTerm[BoolTerm, Term], List[VarTerm[ArrayTerm[ArrayTerm[IntTerm]]]]](
    ("expression", "TypedTerm", "Values"),
    ("a_9[0] == b & b[0] <= 1", a2i9(0) === b1 & b1(0) <= 2, List(a2i9)),
    ("a[0] == b & b[0] <= 2", a2(0) === b2(1) & b2(1)(0) <= 2, List(a2, b2))
  )
  //  format: ON

  //  initialise sequence
  val initSeq = new SMTInit(QF_AUFLIA, List(MODELS))

  for (s ← theSolvers; (txt, t, xr) ← theTerms1 ++ theTerms2) {

    test(s"[${s.name}] configured with ${initSeq.show} to check sat for $txt ") {
      using(new SMTSolver(s, initSeq)) {
        implicit solver ⇒ {
          //  smtlib package eval is used
          val result = isSat(t)
          //  dump values if debug mode
          for (v ← xr) {
            val model = getModel()
            //            println(s"Model: $model")
            val witness = getValue(v)
            //            println(s"[${s.name}] Value of {$v.symbol} is: ${
            //              witness match {
            //                case Success(x) ⇒ x.show;
            //                case Failure(f) ⇒ "Failure: f.getMessage"
            //              }
            //            }")
          }
          result
        }
      } shouldBe Success(Sat())
      //  get a value for each variables in list xr
    }
  }
}