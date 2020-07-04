package org.tygus.suslik.synthesis

import org.scalatest.{BeforeAndAfterAll, FunSuite}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, GoalLabel}
import org.tygus.suslik.logic.{Environment, PFormula, PointsTo, SFormula}
import org.tygus.suslik.synthesis.rules.DelegatePureSynthesis
import org.tygus.suslik.util.SynStats

class CVC4Tests extends FunSuite with SynthesisRunnerUtil with BeforeAndAfterAll {
  override def beforeAll(): Unit = {
    assert(DelegatePureSynthesis.isConfigured())
  }

  val params: SynConfig = defaultConfig.copy(delegatePure = true)
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
    None
  )

  test("Translate ints to SYGUS") {
    val goal = goal1
    val smtTask = DelegatePureSynthesis.toSMTTask(goal)
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
                        |    (=> (and (not (= r 0)) (< x y) ) (and (<= x (target_m r x y)) (<= y (target_m r x y)) )))
                        |(check-synth)""".stripMargin)
  }
  test("Parsing a synthesis fail") {
    val synthRes = DelegatePureSynthesis.invokeCVC(
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
    assert(DelegatePureSynthesis.parseAssignments(
      """(define-fun target_m ((r Int) (x Int) (y Int)) Int y)""") == Map(Expressions.Var("m") -> Expressions.Var("y")))
    assert(DelegatePureSynthesis.parseAssignments(
      """(define-fun target_a1 ((x Int) (y (Set Int))) Int 0)
        |(define-fun target_q ((x Int) (y (Set Int))) (Set Int) x)""".stripMargin) ==
      Map(Expressions.Var("a1") -> IntConst(0), Expressions.Var("q") -> Expressions.Var("x")))
  }

  test("All ints, one existential") {

    val goal = goal1

    val res = DelegatePureSynthesis.PureSynthesisFinal(goal)
    //res.map(_.subgoals.head.pp + "\n").foreach(println)
    assert(res.length == 1)
    assert(res.head.subgoals.size == 1)
    val resGoal: Goal = res.head.subgoals.head
    assert(resGoal.pp == """loc r, int x, int y [][] |-
                        |{not (r == 0) && x < y ; r :-> 0}
                        |  ??
                        |{x <= y && y <= y ; r :-> y}""".stripMargin)
  }
  val goal2 = Goal(
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
    None
  )
  test("Translate goal with set to SyGuS") {
    val smtTask = DelegatePureSynthesis.toSMTTask(goal2)
    assert(smtTask == """(set-logic ALL)
                        |
                        |(define-fun empset () (Set Int) (as emptyset (Set Int)))
                        |
                        |(synth-fun target_v1 ((x Int) (S1 (Set Int)) (v Int) (S (Set Int)) ) Int
                        |  ((Start Int (0 x v ))))
                        |(synth-fun target_S11 ((x Int) (S1 (Set Int)) (v Int) (S (Set Int)) ) (Set Int)
                        |  ((Start (Set Int) (empset S1 S ))))
                        |
                        |(declare-var x Int)
                        |(declare-var S1 (Set Int))
                        |(declare-var v Int)
                        |(declare-var S (Set Int))
                        |
                        |(constraint
                        |    (=> true (= (union (singleton v) S1) (union (singleton (target_v1 x S1 v S)) (target_S11 x S1 v S)))))
                        |(check-synth)""".stripMargin)
  }
  test("Goal with set and int") {
    // loc x [intset S, int v, intset S1][int v1, intset S11] |-
    //{true ; emp}
    //  ??
    //{{v} ++ S1 =i {v1} ++ S11 ; emp}
    val res = DelegatePureSynthesis.PureSynthesisFinal(goal2)
    //res.map(_.subgoals.head.pp + "\n").foreach(println)
    assert(res.length == 1)
    assert(res.head.subgoals.size == 1)
    val resGoal: Goal = res.head.subgoals.head
    assert(resGoal.pp == """loc x [intset S, int v, intset S1][] |-
                           |{emp}
                           |  ??
                           |{{v} ++ S1 =i {v} ++ S1 ; emp}""".stripMargin)
  }

  test("Translating set literal with more than one elem") {
    val lit = SetLiteral(List(IntConst(1), IntConst(2), Expressions.Var("y")))
    val sb = new StringBuilder
    DelegatePureSynthesis.toSmtExpr(lit,Map.empty,sb)
    assert(sb.toString == "(insert 1 2 (singleton y))")
  }
  test ("Translating some missing exprs") {
    //x in S
    val inSet = BinaryExpr(OpIn,Expressions.Var("x"),Expressions.Var("S"))
    val sb = new StringBuilder
    DelegatePureSynthesis.toSmtExpr(inSet,Map.empty,sb)
    assert(sb.toString == "(member x S)")

    //S1 -- S2
    val setDiff = BinaryExpr(Expressions.OpDiff,Expressions.Var("S1"),Expressions.Var("S2"))
    sb.clear()
    DelegatePureSynthesis.toSmtExpr(setDiff,Map.empty,sb)
    assert(sb.toString == "(setminus S1 S2)")

    //Expressions.IfThenElse(cond, left, right)
    val ite = Expressions.IfThenElse(Expressions.BoolConst(true),Expressions.Var("x"),IntConst(3))
    sb.clear()
    DelegatePureSynthesis.toSmtExpr(ite,Map.empty,sb)
    assert(sb.toString == "(ite true x 3)")
  }
  val goal3 = Goal(
    Assertion(PFormula(Set[Expr](UnaryExpr(Expressions.OpNot,BinaryExpr(Expressions.OpEq,Expressions.Var("r"),IntConst(0))),
      BinaryExpr(Expressions.OpEq,Expressions.Var("x"),Expressions.Var("y")))),
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
    None,
    false,
    false
  )
  test("to SMT with exclusions") {
    val smt = DelegatePureSynthesis.toSMTTask(goal3,Some((Expressions.Var("m"),Expressions.Var("x"))))
    assert(smt == """(set-logic ALL)
                    |
                    |(synth-fun target_m ((r Int) (x Int) (y Int) ) Int
                    |  ((Start Int (0 r y ))))
                    |
                    |(declare-var r Int)
                    |(declare-var x Int)
                    |(declare-var y Int)
                    |
                    |(constraint
                    |    (=> (and (not (= r 0)) (= x y) ) (and (<= x (target_m r x y)) (<= y (target_m r x y)) )))
                    |(check-synth)""".stripMargin)
  }
  test("Is there second result") {
    val assignment : Subst = Map(Expressions.Var("m")-> Expressions.Var("y"))
    assert(!DelegatePureSynthesis.hasSecondResult(goal1,assignment))
    assert(DelegatePureSynthesis.hasSecondResult(goal3,assignment))
  }
}
