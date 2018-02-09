package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.Resolver._
import org.tygus.synsl.Synthesis
import org.tygus.synsl.parsing.SynslParser

/**
  * @author Ilya Sergey
  */

class SimpleSynthesisTests extends FunSpec with Matchers {

  val spec1 = "{true; emp} void foo(int* x) {true ; emp}"

  val spec2 = "{true; x :-> a} void foo(int* x) {true ; x :-> a}"

  val spec3 = "{true; x :-> 1} void foo(int* x) {true ; x :-> 43}"

  val spec4 = "{true; x :-> 1 ** y :-> 2} void bar(int* x, int* y) {true ; y :-> 239 ** x :-> 43}"

  val spec5 = "{true; x :-> a ** y :-> 2} void bar(int* x, int* y) {true ; x :-> a ** y :-> 12}"

  val spec6 = "{true; x :-> a ** y :-> 2} void bar(int* x, int* y) {true ; x :-> a ** y :-> a}"

  val spec7 = "{true; x :-> a ** y :-> b} void swap(int* x, int* y) {true ; x :-> b ** y :-> a}"

  val spec8 = "{true; x :-> a ** y :-> c ** z :-> b ** t :-> q } " +
              "void swap (bool* x, int* z, bool* y, int* t) " +
              "{ true; x :-> c ** z :-> b ** t :-> q ** y :-> 41 }"

  val spec9 = "{true; x :-> a ** y :-> c ** z :-> b ** t :-> q } " +
              "void swap (int* x, int* z, int* y, int* t) " +
              "{ true; x :-> q ** z :-> c ** t :-> a ** y :-> b }"

  val spec10 = "{true; x :-> a ** x + 1 :-> b} void swap(int* x, int* y) {true ; x :-> b ** x + 1 :-> a}"

  val spec11 = "{true; x :-> v ** y :-> b ** z :-> v ** v :-> d} " +
      "void kareem1(int * * x, int* y, int* z) " +
      "{true ; x :-> y ** y :-> z ** z :-> x ** v :-> x}"

  val spec12 = "{true; x :-> v ** v :-> d} " +
      "void kareem2(int * * x) " +
      "{true ; x :-> v ** v :-> x}"

  val spec13 = "{true; x :-> a ** a :-> b ** b :-> c ** c :-> 42} " +
      "void kareem3(int * * * * x) " +
      "{true ; x :-> 42 ** b :-> a ** a :-> c ** c :-> b}"

  val spec14 = "{true; x :-> 0} " +
    "void create(int * * x) " +
    "{true ; x :-> y ** y :-> 42 ** [y, 1]}"

  val spec15 = "{true; x :-> 0} " +
    "void create(int * * x) " +
    "{true ; x :-> y ** [y, 3] ** y :-> 1 ** (y + 1) :-> 2 ** (y + 2) :-> x}"

  val spec16 = "{true; x :-> y ** [y, 1] ** y :-> 42} " +
    "void delete(int * * x) " +
    "{true ; x :-> y }"

  val spec17 = "{true; x :-> y ** y :-> 42 ** (y + 1) :-> 43 ** (y + 2) :-> 44 ** [y, 3]} " +
    "void delete(int * * x) " +
    "{true ; x :-> y }"

  val spec18 =
  """
    predicate account(x, amount, limit) {
      | true  =>  x :-> amount ** (x + 1) :-> limit ** [x, 2]
    }

    {true; x :-> y ** account(y, 5, 10)}
      void deleteAccount(int *x)
    {true ; x :-> y }
  """


  import Synthesis._

  private def synthesizeFromSpec(text: String) {
    val parser = new SynslParser
    val res = parser.parseProgram(text)
    assert(res.successful, res)

    val prog = res.get
    assert(prog.decls.nonEmpty)
    val (goals, env) = resolveProgram(prog)

    assert(goals.lengthCompare(1) == 0, "Expected a single synthesis goal")

    val goal = goals.head
    val sresult = synthesizeProc(goal, env)

    sresult match {
      case Some(res) =>
        println("Specification:\n")
        println(s"${goal.pp}\n")
        println("Successfully synthesised:")
        println(s"${res.pp}")
        println("-----------------------------------------------------\n")
      case None =>
        assert(false, s"Failed to synthesise:\n$sresult")
    }
  }

  describe("SL-based synthesizer") {
    it("should be able to synthesize an empty program") {
      // Testing [emp]
      synthesizeFromSpec(spec1)
    }

    it("should be able to synthesize an empty program with constant footprint") {
      // Testing [frame]
      synthesizeFromSpec(spec2)
    }

    it("should be able to synthesize a simple constant-assigning procedure") {
      // Testing [write]
      synthesizeFromSpec(spec3)
    }

    it("should be able to synthesize a two-pointer constant-assigning procedure") {
      // Testing [write]
      synthesizeFromSpec(spec4)
    }

    it("should be able to use [frame] and [write]") {
      // Testing [frame] and [write]
      synthesizeFromSpec(spec5)
    }

    it("should be able to synthesize a program with read") {
      // Testing [read], [frame] and [write]
      synthesizeFromSpec(spec6)
    }

    it("should be able to synthesize a swap program") {
      // Testing [read], [frame] and [write]
      synthesizeFromSpec(spec7)
    }

    it("should be able to synthesize a non-trivial swap program") {
      // Testing [read], [frame] and [write]
      synthesizeFromSpec(spec8)
    }

    it("should be able to synthesize a more complex swap program") {
      // Testing [read], [frame] and [write]
      synthesizeFromSpec(spec9)
    }

    it("should be able to work with pointer offsets") {
      // Testing [read], [frame] and [write]
      synthesizeFromSpec(spec10)
    }

    it("should be able to work with Kareem's example") {
      synthesizeFromSpec(spec11)
    }

    it("should be able to work with a simple version of Kareem's example") {
      synthesizeFromSpec(spec12)
    }

    it("should be able to work with crazy indirection") {
      synthesizeFromSpec(spec13)
    }

    it("should be able to allocate memory") {
      synthesizeFromSpec(spec14)
    }

    it("should be able to allocate blocks") {
      synthesizeFromSpec(spec15)
    }

    it("should be able to deallocate memory") {
      synthesizeFromSpec(spec16)
    }

    it("should be able to deallocate blocks") {
      synthesizeFromSpec(spec17)
    }

    it("should be able to deallocate structs") {
      synthesizeFromSpec(spec18)
    }
  }

}
