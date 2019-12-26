package org.tygus.suslik.parsing

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.util.SynLogLevels

/**
  * @author Roman Shchedrin
  */

class ParserErrorsTests extends FunSpec with Matchers {

  val log = SynLogLevels.Test

  import log._

  val pred1 =
    """predicate lseg (loc x, loc y) {
      | x == y  =>  {emp}
      | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
      }

      {emp} void foo (loc x) {emp}
    """

  def failsOnLine(code: String, line_no: Int) {
    val parser = new SSLParser
    val result = parser.parseGoal(code)
    assert(!result.successful, "Parser should fail on line " + line_no + "in code \n" + code)
    result match {
      case parser.Failure(msg, next) => assert(next.pos.line == line_no,
        "\nCode\n" + code + "\nshould fail on line " + line_no + " but failed on " + next.pos.line + "\nmessage: " + result)
      case other => assert(false, other)
    }
  }

  describe("Parser syntax errors") {
    it("should fail with syntax error - 1") {
      val code = //                    V
        """predicate lseg (loc x, loc y {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 1)
    }

    it("should fail with syntax error - 2") {
      val code = //                     V
        """predicate lseg (loc x, loc y)
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 2)
    }
    it("should fail with syntax error - 3") {
      val code =
        """peace lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 1)
    }
    it("should fail with syntax error - 4") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x === y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 2)
    }
    it("should fail with syntax error - 5") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x ==   =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 2)
    }
    it("should fail with syntax error - 6") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {ep}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 2)
    }

    it("should fail with syntax error - 7") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 2)
    }

    it("should fail with syntax error - 8") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :- v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 3)
    }
    it("should fail with syntax error - 9") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          {

          {emp} void foo (loc x) {emp}
        """
      failsOnLine(code, 4)
    }
    it("should fail with syntax error - 10") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp void foo (loc x) {emp}
        """
      failsOnLine(code, 6)
    }
    it("should fail with syntax error - 11") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} vid foo (loc x) {emp}
        """
      failsOnLine(code, 6)
    }
    it("should fail with syntax error - 12") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo loc x) {emp}
        """
      failsOnLine(code, 6)
    }
    it("should fail with syntax error - 13") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x {emp}
        """
      failsOnLine(code, 6)
    }
    it("should fail with syntax error - 14") {
      val code =
        """predicate lseg (loc x, loc y) {
          | x == y  =>  {emp}
          | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
          }

          {emp} void foo (loc x) {emp"""
      failsOnLine(code, 6)
    }

    it("should throw exception if no goal is given") {
      val code =
        """predicate lseg(loc x, set s) {
        |  x == 0        => { s =i {} ; emp }
        |  not (x == 0)  => { s =i {v} ++ s1 ; [x, 2] ** x :-> v ** (x + 1) :-> nxt ** lseg(nxt, s1) }
      }"""
      intercept[SynthesisException] {
        val parser = new SSLParser
        val result = parser.parseGoal(code)
      }
    }
  }


}

