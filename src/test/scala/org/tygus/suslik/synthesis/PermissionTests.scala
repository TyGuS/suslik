package org.tygus.suslik.synthesis

import org.scalatest.FunSuite
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Preprocessor.pTrue
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic.{Environment, FunSpec, PFormula, PointsTo, SFormula}
import org.tygus.suslik.util.SynStats

class PermissionTests extends FunSuite with SynthesisRunnerUtil  {
  val params: SynConfig = defaultConfig.copy(traceLevel = 1)

  //loc r |-
  //{r :-> 0}
  //  ??
  //{r :-> 1}
  val spec1 = FunSpec("test1", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0))))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1)))))  //post
  )

  test("Can write if both heaplets mutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec1, env, Hole)
    assert(sresult._1.nonEmpty)
  }

  val spec2 = FunSpec("test2", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),PermConst(Permissions.Immutable))))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1),PermConst(Permissions.Immutable)))))  //post
  )

  test("Cannot write if both heaplets immutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec2, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec3 = FunSpec("test3", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),PermConst(Permissions.Mutable))))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1),PermConst(Permissions.Immutable)))))  //post
  )

  test("Cannot write if one is immutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec3, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec4 = FunSpec("test4", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),PermConst(Permissions.Mutable))))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),PermConst(Permissions.Immutable)))))  //post
  )

  test("Cannot unify if different mutability") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec4, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec5 = FunSpec("test5", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),Var("a"))))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1),Var("a")))))  //post
  )

  test("Cannot write if permission is unknown") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec5, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec6 = FunSpec("test6", VoidType,
    List((Var("r"), LocType)),
    Assertion(PFormula(Var("a") |=| PermConst(Permissions.Mutable)), SFormula(List(PointsTo(Var("r"),0,IntConst(0),Var("a"))))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1),Var("a")))))  //post
  )

  test("Can write if permission is symbolic but known") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec6, env, Hole)
    assert(sresult._1.nonEmpty)
  }

}
