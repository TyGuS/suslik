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

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.configurations.SMTLogics.QF_LIA
import org.bitbucket.franck44.scalasmt.configurations.SMTOptions.{INTERPOLANTS, MODELS}
import org.bitbucket.franck44.scalasmt.interpreters.{Resources, SMTSolver}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax.{Sat, UnSat}
import org.bitbucket.franck44.scalasmt.theories.{Core, IntegerArithmetics}
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, Model}
import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.{FunSuite, Matchers}

import scala.util.{Failure, Success, Try}

/**
  * @author Ilya Sergey
  */

class ScalaSmtTest extends FunSuite with TableDrivenPropertyChecks with Matchers
    with Core with IntegerArithmetics with Commands with Resources {

  val x = Ints("x")
  val y = Ints("y")
  val z = Ints("z")

  test( """| Z3 example
           | (set-option :produce-models true)
           | (set-logic QF_LIA)
           | (declare-fun x () Int)
           | (declare-fun y () Int)
           | (assert (<= (+ x 1) y))
           | (assert (and (= (mod y 4) 3) (>= y 2)))
           | ;; Check SAT
           | (check-sat)
           | ;; returns sat
           | ;; Get values for x and y
           | (get-value (x y))
           | ;; returns ((x 2) (y 3))
           | """.stripMargin ) {
      //  ScalaSMT version
      val result : Try[ Model ] =
          using( new SMTSolver( "Z3", new SMTInit( QF_LIA, List( MODELS ) ) ) ) {
              implicit withSolver ⇒
                  isSat(
                      x + 1 <= y,
                      y % 4 === 3 & y >= 2 ) match {
                          case Success( Sat() ) ⇒ getModel()
                          case _                ⇒ Failure( new Exception( "failed" ) )
                      }
          }

      result match {
          case Success( m ) ⇒
              ( m.valueOf( x ), m.valueOf( y ) ) match {
                  case ( Some( valx ), Some( valy ) ) ⇒
                      val v = Map( x -> valx.show.toInt, y -> valy.show.toInt )
                      assert( v( x ) + 1 == v( y ) && v( y ) % 4 == 3 & v( y ) >= 2 )

                  case _ ⇒ fail( new Exception( s"Could not get value from model for Example 1. $m" ) )
              }

          case Failure( f ) ⇒ fail( new Exception( s"Could not get model for Example 1. ${f.getMessage}" ) )
      }

  }


}
