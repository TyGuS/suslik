package org.tygus.suslik.synthesis

import org.scalatest.FunSuite
import org.tygus.suslik.language.Expressions.{BinaryExpr, Expr, IntConst, SetLiteral, UnaryExpr}
import org.tygus.suslik.language.{Expressions, IntSetType, IntType, LocType, Statements}
import org.tygus.suslik.logic.{Environment, Gamma, PFormula, PointsTo, SFormula}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, GoalLabel}
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.synthesis.rules.PureSynthesis
import org.tygus.suslik.synthesis.rules.UnificationRules.Pick
import org.tygus.suslik.util.SynStats

class CVC4Tests extends FunSuite with SynthesisRunnerUtil {
  val params: SynConfig = defaultConfig
  //loc r, int x, int y [int m] |-
  //{not (r == 0) && x < y ; r :-> 0}
  //  ??
  //{x <= m && y <= m ; r :-> m}
  val goal1 = Goal(
    Assertion(PFormula(Set[Expr](UnaryExpr(Expressions.OpNot,BinaryExpr(Expressions.OpEq,Expressions.Var("r"),IntConst(0))),
      BinaryExpr(Expressions.OpLt,Expressions.Var("x"),Expressions.Var("y")))),
      SFormula(List(PointsTo(Expressions.Var("r"),0,IntConst(0))))), //pre
    Assertion(PFormula(Set[Expr](BinaryExpr(Expressions.OpLeq,Expressions.Var("x"),Expressions.Var("m")),
      BinaryExpr(Expressions.OpLeq,Expressions.Var("y"),Expressions.Var("m")))),
      SFormula(List(PointsTo(Expressions.Var("r"),0,Expressions.Var("m"))))), //post
    Map(Expressions.Var("r") -> LocType,
      Expressions.Var("x") -> IntType,
      Expressions.Var("y") -> IntType,
      Expressions.Var("m") -> IntType),
    List(Expressions.Var("r"), Expressions.Var("x"),Expressions.Var("y")),
    Set(),
    "maxish",
    GoalLabel(List(1), Nil),
    None,
    Environment(Map.empty, Map.empty, params, new SynStats(params.timeOut)),
    Statements.Hole,
    false,
    false
  )

  test("Translate ints to SYGUS") {
    val goal = goal1
    val smtTask = PureSynthesis.toSMTTask(goal)
    assert(smtTask == """(set-logic ALL)
                        |
                        |(synth-fun target_m ((r Int) (x Int) (y Int) ) Int
                        |  ((Start Int (0 r x y ))))
                        |
                        |(declare-var r Int)
                        |(declare-var x Int)
                        |(declare-var y Int)
                        |
                        |(constraint
                        |    (=> (and (not (= r 0) ) (< x y) ) (and (<= x (target_m r x y)) (<= y (target_m r x y)) )))
                        |(check-synth)""".stripMargin.replaceAllLiterally("\r\n","\n"))
  }
  test("Parsing a synthesis fail") {
    val synthRes = PureSynthesis.invokeCVC(
    """(set-logic ALL)
      |
      |(synth-fun target_m ((r Int) (x Int) (y Int)) Int
      |  ((Start Int (0 r x y))))
      |
      |
      |(declare-var r Int)
      |(declare-var x Int)
      |(declare-var y Int)
      |
      |; exists v2  [= (target x y)]
      |(constraint
      |    (=> (and (not (= r 0)) (< x y)) (and (> x (target_m r x y)) (<= y (target_m r x y)))))
      |
      |
      |
      |(check-synth)""".stripMargin)
    assert(synthRes == None)
  }

  test("Parse CVC4 synthesis results") {
    assert(PureSynthesis.parseAssignments(
      """(define-fun target_m ((r Int) (x Int) (y Int)) Int y)""") == Map(Expressions.Var("m") -> Expressions.Var("y")))
    assert(PureSynthesis.parseAssignments(
      """(define-fun target_a1 ((x Int) (y (Set Int))) Int 0)
        |(define-fun target_q ((x Int) (y (Set Int))) (Set Int) x)""".stripMargin) ==
      Map(Expressions.Var("a1") -> IntConst(0), Expressions.Var("q") -> Expressions.Var("x")))
  }

  test("All ints, one existential") {

    val goal = goal1

    val res = PureSynthesis(goal)
    //res.map(_.subgoals.head.pp + "\n").foreach(println)
    assert(!res.isEmpty)
    val resGoal: Goal = res.get
    assert(goal.pp == """loc r, int x, int y [] |-
                        |{not (r == 0) && x < y ; r :-> 0}
                        |  ??
                        |{x <= y && y <= y ; r :-> y}""".stripMargin)
  }

  test("Goal with set and int") {
    // {true ; emp}??{{v} ++ S1 =i {v1} ++ S11 ; emp}
    val goal = Goal(
      Assertion(PFormula(Set[Expr]()),SFormula(Nil)), //pre
      Assertion(PFormula(Set[Expr](BinaryExpr(Expressions.OpSetEq,BinaryExpr(Expressions.OpUnion,SetLiteral(List(Expressions.Var("v"))),Expressions.Var("S1")),
                                                                  BinaryExpr(Expressions.OpUnion, SetLiteral(List(Expressions.Var("v1"))),Expressions.Var("S11"))))),
        SFormula(Nil)), //post
      Map(Expressions.Var("x") -> LocType,
        Expressions.Var("S1") -> IntSetType,
        Expressions.Var("v") -> IntType,
        Expressions.Var("S11") -> IntSetType,
        Expressions.Var("S") -> IntSetType,
        Expressions.Var("v1") -> IntType),
      List(Expressions.Var("x")),
      Set(Expressions.Var("S"), Expressions.Var("v"), Expressions.Var("S1")),
      "foo",
      GoalLabel(List(1), Nil),
      None,
      Environment(Map.empty, Map.empty, params,new SynStats(params.timeOut)),
      Statements.Hole,
      false,
      false
    )
  }
}
