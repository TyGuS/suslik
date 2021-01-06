package org.tygus.suslik.synthesis

import java.io.PrintWriter
import java.nio.file.Paths

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.language.Expressions.{IntConst, Subst, Var}
import org.tygus.suslik.language.{LocType, VoidType}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.{Environment, PointsTo}
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.synthesis.Evaluator.{Heap, evaluate}
import org.tygus.suslik.util.SynStats

import scala.collection.immutable.TreeSet

class RandomizedTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit = {
    super.doRun(testName, desc, in, out, params)
    it(desc) {
      synthesizeFromSpec(testName, in, out, params)
    }
  }

  describe("randomly generates specifications for suslik and runs the evaluator on the synthesized program") {
    }
    it("passes random testing") {

      val s: Statement = Load(Var("v"), LocType, Var("x"))
      val store: Subst = Map(Var("x") -> IntConst(123), Var("y") -> IntConst(234), Var("z") -> IntConst(345), Var("t") -> IntConst(456))
      val pre_heap: Heap = Map(123 -> IntConst(1), 234 -> IntConst(2), 345 -> IntConst(3), 456 -> IntConst(4))
      val post_heap: Heap = Map(123 -> IntConst(4), 234 -> IntConst(3), 345 -> IntConst(2), 456 -> IntConst(1) )

      val params = defaultConfig
      val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
      val synthesizer = createSynthesizer(env)
//      val pre_ls =
      val pre = new Assertion(new org.tygus.suslik.logic.PFormula(TreeSet()), org.tygus.suslik.logic.SFormula(List(PointsTo(Var("x"),0,Var("a")), PointsTo(Var("y"),0,Var("c")), PointsTo(Var("z"),0,Var("b")), PointsTo(Var("t"),0,Var("q")))))
      val post = Assertion(new org.tygus.suslik.logic.PFormula(TreeSet()), org.tygus.suslik.logic.SFormula(List(PointsTo(Var("x"),0,Var("q")), PointsTo(Var("z"),0,Var("c")), PointsTo(Var("t"),0,Var("a")), PointsTo(Var("y"),0,Var("b")))))
      val spec = org.tygus.suslik.logic.FunSpec("test", VoidType, List((Var("x"),LocType), (Var("z"),LocType), (Var("y"),LocType), (Var("t"),LocType)), pre, post)
      env.stats.start()
      val sresult = synthesizer.synthesizeProc(spec, env, Hole, (List(), List()))
      val duration = env.stats.duration

      val se = sresult._1 match {
        case Nil =>
          throw SynthesisException(s"Failed to synthesise:\n$sresult")
        case procs =>
            val funstr = procs.map(proc => proc match {
              case Procedure(f, _) => f.pp
            })
            val bodystr = procs.map(proc => proc match {
              case Procedure(_, body) => body.pp
            })
            val s = "Function spec:  " + funstr.mkString("\n") + "\n\n" +
              "Body:  " + bodystr.mkString("\n") + "\n\n" +
              procs.map(_.pp.trim).mkString("\n\n") + "\n" +
              "AST for Pre: \n" + procs.head.f.pre.toString() + "\n\n" +
              "AST for Post: \n" + procs.head.f.post.toString() + "\n\n" +
              "AST for Body: \n" + procs.head.body.toString()
          println(s)
          val synthesized_as_stmts = procs.map(proc => proc match{
            case Procedure(_, body) => body
          })
          val synthesized = synthesized_as_stmts.foldLeft(Skip.asInstanceOf[Statement])(SeqComp)
          synthesized
      }
      println(se)
      assert(evaluate(se, pre_heap, store)._1 == post_heap)
    }

}