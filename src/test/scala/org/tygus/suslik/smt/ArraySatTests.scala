package org.tygus.suslik.smt

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
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, TypedTerm}
import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.{FunSuite, Matchers}
import org.tygus.suslik.logic

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

  logic.smt.disableLogging()

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

  val x = Ints("x")

  //  format: OFF
  val theTerms = Table[String, TypedTerm[BoolTerm, Term], SatResponses, SMTLogics.Value](
    ("expression", "TypedTerm", "Expected status", "logic"),
    ("a == b", a1 === b1, Sat(), QF_AUFLIA),
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
      } shouldBe {
        Success(r)
      }
    }
  }
}

