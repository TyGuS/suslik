package org.tygus.suslik.overloading

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Preprocessor.preprocessProgram
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.synthesis._
import org.tygus.suslik.util.SynStats

/**
  * @author Roman Shchedrin
  */

class OverloadedOperatorsTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  def resolveFromSpec(testName: String, text: String, out: String = "nope", params: SynConfig = defaultConfig): Specifications.Goal = {
    val parser = new SSLParser(params)
    val res = parser.parseGoal(text)
    if (!res.successful) {
      throw SynthesisException(s"Failed to parse the input:\n$res")
    }
    val prog = res.get
    val (specs, predEnv, funcEnv, body) = preprocessProgram(prog, params)
    if (specs.lengthCompare(1) != 0) {
      throw SynthesisException("Expected a single synthesis goal")
    }
    val spec = specs.head
    val FunSpec(name, _, formals, pre, post, var_types) = spec
    val env = Environment(predEnv, funcEnv, params, new SynStats(params.timeOut))
    val goal = topLevelGoal(pre, post, formals, name, env, body, var_types)
    goal
  }

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("Resolver tests") {
    it("should respect function signature") {
      val code =
        """
          {emp} void foo (int i, bool b, loc l, set s){ emp}
        """

      val goal = resolveFromSpec("foo", code)
      assert(goal.gamma(Var("i")) == IntType)
      assert(goal.gamma(Var("l")) == LocType)
      assert(goal.gamma(Var("s")) == IntSetType)
      assert(goal.gamma(Var("b")) == BoolType)
    }

    it("should resolve ambiguity as loc by default") {
      val code =
        """
          {emp} void foo (int v){ www==www;emp}
        """

      val goal = resolveFromSpec("foo", code)
      assert(goal.gamma(Var("www")) == LocType)
    }

    it("should resolve type from equality chain") {
      val code =
        """
          {bb == ((a/\b) == (b \/ a))/\cc==bb/\dd==cc
          /\ i == 5 /\ j == i; emp}
          void foo (int v)
          { ee==dd /\ k == j;emp}
        """

      val goal = resolveFromSpec("foo", code)
      assert(goal.gamma(Var("a")) == BoolType)
      assert(goal.gamma(Var("b")) == BoolType)
      assert(goal.gamma(Var("bb")) == BoolType)
      assert(goal.gamma(Var("cc")) == BoolType)
      assert(goal.gamma(Var("dd")) == BoolType)
      assert(goal.gamma(Var("ee")) == BoolType)
      assert(goal.gamma(Var("i")) == IntType)
      assert(goal.gamma(Var("j")) == IntType)
      assert(goal.gamma(Var("k")) == IntType)
    }

    it("should be able to resolve sets from intervals") {
      val code =
        """
          {i1 == [x..y] && i2 == [x] && i3 == [] && s1 == {x, y} && s2 == {}; emp}
          void interval_test(int x, int y)
          {lower i1 == lower i2 && x in i1 && x in s1 && x in (i1 + i2) && x in (s1 + s2); emp}
        """

      val goal = resolveFromSpec("interval_test", code)
      assert(goal.gamma(Var("i1")) == IntervalType)
      assert(goal.gamma(Var("i2")) == IntervalType)
      assert(goal.gamma(Var("i3")) == IntervalType)
      assert(goal.gamma(Var("s1")) == IntSetType)
      assert(goal.gamma(Var("s2")) == IntSetType)
    }

  }

  describe("Overloaded operators tests") {
    runAllTestsFromDir("overloaded-ops")
  }

}
