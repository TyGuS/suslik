package org.tygus.suslik.synthesis

import java.io.PrintWriter
import java.nio.file.Paths

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.language.Expressions.{IntConst, Subst, Var}
import org.tygus.suslik.language.{LocType, VoidType}
import org.tygus.suslik.language.Statements.{Hole, Load, Procedure, Statement}
import org.tygus.suslik.logic.Environment
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
    it("evaluates Load correctly") {

      val s: Statement = Load(Var("v"), LocType, Var("x"))
      val store: Subst = Map(Var("v") -> IntConst(567), Var("x") -> IntConst(123))
      val pre_heap: Heap = Map(123 -> IntConst(456), 567 -> IntConst(789))
      val post_heap: Heap = Map(123 -> IntConst(456), 567 -> IntConst(456))

      val params = defaultConfig
      val env = Environment(Map(), Map(), params, new SynStats(params.timeOut))
      val synthesizer = createSynthesizer(env)
      val pre = new Assertion(new org.tygus.suslik.logic.PFormula(TreeSet()), org.tygus.suslik.logic.SFormula(List()))
      val post = Assertion(new org.tygus.suslik.logic.PFormula(TreeSet()), org.tygus.suslik.logic.SFormula(List()))
      val spec = org.tygus.suslik.logic.FunSpec("test", VoidType, List(), pre, post)
      env.stats.start()
      val sresult = synthesizer.synthesizeProc(spec, env, Hole)
      val duration = env.stats.duration

      val se = sresult._1 match {
        case Nil =>
          throw SynthesisException(s"Failed to synthesise:\n$sresult")
        case procs =>
          val result = if (params.printSpecs) {
            procs.map(p => {
              val (pre, post) = (p.f.pre.pp.trim, p.f.post.pp.trim)
              List(pre, post, p.pp.trim).mkString("\n")
            }).mkString("\n\n")
          } else {
            val funstr = procs.map(proc => proc match {
              case Procedure(f, _) => f.pp
            })
            val bodystr = procs.map(proc => proc match {
              case Procedure(_, body) => body.pp
            })
            "Function spec:  " + funstr.mkString("\n") + "\n\n" +
              "Body:  " + bodystr.mkString("\n") + "\n\n" +
              procs.map(_.pp.trim).mkString("\n\n") + "\n" +
              "AST for Pre: \n" + procs.head.f.pre.toString() + "\n\n" +
              "AST for Post: \n" + procs.head.f.post.toString() + "\n\n" +
              "AST for Body: \n" + procs.head.body.toString()
          }
      }
      println(se)
      assert(evaluate(s, pre_heap, store) == post_heap)
    }

}