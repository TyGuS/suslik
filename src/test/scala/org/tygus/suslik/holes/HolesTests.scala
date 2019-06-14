package org.tygus.suslik.holes

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Resolver.resolveProgram
import org.tygus.suslik.logic.Specifications.{Goal, makeNewGoal}
import org.tygus.suslik.logic._
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.util.OtherUtil.Accumulator

/**
  * @author Roman Shchedrin
  */

class HolesTests extends FunSpec with Matchers with SynthesisRunnerUtil  {

  val synthesis: Synthesis = new PhasedSynthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }

  private def fillHoles(text:String) = {
    val parser = new SSLParser
    val res = parser.parseGoalSUS(text)
    if (!res.successful) {
      throw SynthesisException(s"Failed to parse the input:\n$res")
    }

    val prog = res.get
    val (specs, env, body) = resolveProgram(prog)

    if (specs.lengthCompare(1) != 0) {
      throw SynthesisException("Expected a single synthesis goal")
    }

    val spec = specs.head
    val time1 = System.currentTimeMillis()

    val FunSpec(name, tp, formals, pre, post, var_decl) = spec
    val goal = makeNewGoal(pre, post, formals, name, env, var_decl)
    val subGoalsAcc = new Accumulator[Goal]()
    val corrGoalsAcc = new Accumulator[Goal]()
    val specifiedBody = synthesis.propagatePre(goal, body, subGoalsAcc , corrGoalsAcc)
    val subGoals =  subGoalsAcc.get
    val correctness_goals = corrGoalsAcc.get
    (specifiedBody, subGoals, correctness_goals)
  }

  private def assertEqualExceptWhitespace(s1:String, s2:String)={
    assert(s1.replaceAll("\\s", "") == s2.replaceAll("\\s", ""))
  }


  describe("Holes to goals tests") {
    it("should synthesize partial swap"){
      val text = """void swap(loc x, loc y)
{ x :-> a ** y :-> b }
{ x :-> b ** y :-> a }
{
  let yyy = *y;
  ??
}"""
      val (specifiedBody, subGoals, correctness_goals) = fillHoles(text)
      print(specifiedBody.pp)
      val expectedBody = """  let yyy = *y;
                             <??
                               int yyy, loc x, loc y |-
                               {true && yyy == b; x :-> a ** y :-> yyy}
                               {true && yyy == b; y :-> a ** x :-> yyy}
                             ??>"""
      assertEqualExceptWhitespace(specifiedBody.pp, expectedBody)
      assert(correctness_goals.isEmpty)
      assert(subGoals.size == 1)
      assertEqualExceptWhitespace(subGoals.head.pp, """
                                     int yyy, loc x, loc y |-
                                     {true && yyy == b; x :-> a ** y :-> yyy}
                                     {true && yyy == b; y :-> a ** x :-> yyy}""")
    }
  }

  describe("Holes tests") {
    runAllTestsFromDir("holes")
  }

}
