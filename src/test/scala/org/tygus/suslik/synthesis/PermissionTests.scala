package org.tygus.suslik.synthesis

import org.scalatest.FunSuite
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Preprocessor.pTrue
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic.{Block, Environment, FunSpec, PFormula, PointsTo, SFormula}
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
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),eImm)))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1),eImm))))  //post
  )

  test("Cannot write if both heaplets immutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec2, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec3 = FunSpec("test3", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),eMut)))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1),eImm))))  //post
  )

  test("Cannot write if one is immutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec3, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec4 = FunSpec("test4", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),eMut)))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(0),eImm))))  //post
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
    Assertion(PFormula(Var("a") |=| eMut), SFormula(List(PointsTo(Var("r"),0,IntConst(0),Var("a"))))), //pre
    Assertion(pTrue, SFormula(List(PointsTo(Var("r"),0,IntConst(1),Var("a")))))  //post
  )

  test("Can write if permission is symbolic but known") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec6, env, Hole)
    assert(sresult._1.nonEmpty)
  }

  val spec7 = FunSpec("test7", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(Block(Var("r"), 2, eImm), PointsTo(Var("r"),0,IntConst(0)), PointsTo(Var("r"),1,IntConst(1))))), //pre
    Assertion(pTrue, SFormula(List()))  //post
  )

  test("Cannot deallocate when block is immutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec7, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec8 = FunSpec("test8", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(Block(Var("r"), 2), PointsTo(Var("r"),0,IntConst(0), eImm), PointsTo(Var("r"),1,IntConst(1))))), //pre
    Assertion(pTrue, SFormula(List()))  //post
  )

  test("Cannot deallocate when some pointer inside the block is immutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec8, env, Hole)
    assert(sresult._1.isEmpty)
  }

  val spec9 = FunSpec("test9", VoidType,
    List((Var("r"), LocType)),
    Assertion(pTrue, SFormula(List(Block(Var("r"), 2), PointsTo(Var("r"),0,IntConst(0)), PointsTo(Var("r"),1,IntConst(1))))), //pre
    Assertion(pTrue, SFormula(List()))  //post
  )

  test("Can deallocate when everything inside the block is mutable") {
    val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
    val synthesizer = createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec9, env, Hole)
    assert(sresult._1.nonEmpty)
  }
}
