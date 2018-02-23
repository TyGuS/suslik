package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.logic.Resolver._
import org.tygus.synsl.parsing.SynslParser

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

abstract class SynthesisTests extends FunSpec with Matchers {

  val synthesis: Synthesis

  import synthesis._

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

  val accountPred =
    """
    predicate account(x, amount, limit) {
      | true  =>  x :-> limit ** (x + 1) :-> amount ** [x, 2]
    }

    """

  val spec18 = accountPred ++
      """
      {true; x :-> y ** account(y, 5, 10)}
        void deleteAccount(int *x)
      {true ; x :-> y }
    """

  val spec19 = accountPred ++
      """
    {true; x :-> 0}
      void createAccount(int *x, int bal, int lim)
    {true ; x :-> y ** account(y, bal, lim) }
   """

  val spec20 = accountPred ++
      """
    {true; x :-> y ** account(y, bal, lim)}
      void deposit(int *x, int amount)
    {true ; x :-> y ** account(y, bal + amount, lim) }
   """

  // Incorporating entailment checking (borrowing from another testsuite):

  val spec21 =  "{(x == x) /\\ (y == x) ; x :-> 3} void bar(int *x, int y) { (x == x) /\\ ((x == y) /\\ true) ; x :-> 3}"

  val spec22 =  "{ y == x ; x :-> a} void bar(int *x, int y) { (x == x) /\\ (x == y) ; x :-> 4}"


  private def synthesizeFromSpec(text: String, out: String = "nope") {
    val parser = new SynslParser
    val res = parser.parseGoal(text)
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
        val result = res.pp
        println(s"${result}")
        println("-----------------------------------------------------\n")

        if (out != "nope") {
          val tt = out.stripMargin.trim
          assert(result.trim == tt, s"\nThe expected output\n${tt}\ndoesn't match the result:\n${result.trim}")
        }
      case None =>
        assert(false, s"Failed to synthesise:\n$sresult")
    }
  }

  describe("SL-based synthesizer") {
    it("should be able to synthesize an empty program") {
      // Testing [emp]
      val out = """void foo (int * x) {
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec1, out)
    }

    it("should be able to synthesize an empty program with constant footprint") {
      // Testing [frame]
      val out = """void foo (int * x) {
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec2, out)
    }

    it("should be able to synthesize a simple constant-assigning procedure") {
      // Testing [write]
      val out = """void foo (int * x) {
                  |  *x = 43;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec3, out)
    }

    it("should be able to synthesize a two-pointer constant-assigning procedure") {
      // Testing [write]
      val out = """void bar (int * x, int * y) {
                  |  *x = 43;
                  |  *y = 239;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec4, out)
    }

    it("should be able to use [frame] and [write]") {
      // Testing [frame] and [write]
      val out = """void bar (int * x, int * y) {
                  |  *y = 12;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec5, out)
    }

    it("should be able to synthesize a program with read") {
      // Testing [read], [frame] and [write]
      val out = """void bar (int * x, int * y) {
                  |  let a2 = *x;
                  |  *y = a2;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec6, out)
    }

    it("should be able to synthesize a swap program") {
      // Testing [read], [frame] and [write]
      val out = """void swap (int * x, int * y) {
                  |  let a2 = *x;
                  |  let b2 = *y;
                  |  *x = b2;
                  |  *y = a2;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec7, out)
    }

    it("should be able to synthesize a non-trivial swap program") {
      // Testing [read], [frame] and [write]
      val out = """void swap (bool * x, int * z, bool * y, int * t) {
                  |  let c2 = *y;
                  |  *x = c2;
                  |  *y = 41;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec8, out)
    }

    it("should be able to synthesize a more complex swap program") {
      // Testing [read], [frame] and [write]
      val out = """void swap (int * x, int * z, int * y, int * t) {
                  |  let a2 = *x;
                  |  let c2 = *y;
                  |  let b2 = *z;
                  |  let q2 = *t;
                  |  *x = q2;
                  |  *y = b2;
                  |  *z = c2;
                  |  *t = a2;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec9, out)
    }

    it("should be able to work with pointer offsets") {
      // Testing [read], [frame] and [write]
      val out = """void swap (int * x, int * y) {
                  |  let a2 = *x;
                  |  let b2 = *(x + 1);
                  |  *x = b2;
                  |  *(x + 1) = a2;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec10, out)
    }

    it("should be able to work with Kareem's example") {
      val out = """void kareem1 (int * * x, int * y, int * z) {
                  |  let v2 = *x;
                  |  *x = y;
                  |  *y = z;
                  |  *z = x;
                  |  *v2 = x;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec11, out)
    }

    it("should be able to work with a simple version of Kareem's example") {
      val out =
        """void kareem2 (int * * x) {
          |  let v2 = *x;
          |  *v2 = x;
          |  skip;
          |}"""
      synthesizeFromSpec(spec12, out)
    }

    it("should be able to work with crazy indirection") {
      val out = """void kareem3 (int * * * * x) {
                  |  let a2 = *x;
                  |  let b2 = *a2;
                  |  let c2 = *b2;
                  |  *x = 42;
                  |  *a2 = c2;
                  |  *b2 = a2;
                  |  *c2 = b2;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec13)
    }

    it("should be able to allocate memory") {
      val out = """void create (int * * x) {
                  |  let y2 = malloc(1);
                  |  *x = y2;
                  |  *y2 = 42;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec14)
    }

    it("should be able to allocate blocks") {
      val out = """void create (int * * x) {
                  |  let y2 = malloc(3);
                  |  *x = y2;
                  |  *y2 = 1;
                  |  *(y2 + 1) = 2;
                  |  *(y2 + 2) = x;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec15, out)
    }

    it("should be able to deallocate memory") {
      val out = """void delete (int * * x) {
                  |  let y2 = *x;
                  |  free(y2);
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec16, out)
    }

    it("should be able to deallocate blocks") {
      val out = """void delete (int * * x) {
                  |  let y2 = *x;
                  |  free(y2);
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec17, out)
    }

    it("should be able to deallocate structs") {
      val out = """void deleteAccount (int * x) {
                  |  let y2 = *x;
                  |  free(y2);
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec18, out)
    }

    it("should be able to allocate structs") {
      val out = """void createAccount (int * x, int bal, int lim) {
                  |  let y2 = malloc(2);
                  |  *x = y2;
                  |  *y2 = lim;
                  |  *(y2 + 1) = bal;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec19, out)
    }

    it("should be able to update structs") {
      val out = """void deposit (int * x, int amount) {
                  |  let y2 = *x;
                  |  let bal2 = *(y2 + 1);
                  |  *(y2 + 1) = bal2 + amount;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec20)
    }
  }

  describe("SL-based synthesizer with entailment") {
    it("should be able to synthesize an empty program for a non-trivial pure part") {
      // Testing [Hypothesis]
      val out = """void bar (int * x, int y) {
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec21)
    }

    it("should be able to get rid of tautologies in the post") {
      // Testing [=-R]
      val out = """void bar (int * x, int y) {
                  |  *x = 4;
                  |  skip;
                  |}"""
      synthesizeFromSpec(spec22)
    }
  }


}
