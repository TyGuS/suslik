package org.tygus.suslik.certification.targets.vst

import java.nio.file.Paths
import java.io.{File, PrintWriter}

import org.tygus.suslik.certification.{CertTree, Certificate, CertificateOutput, CertificationTarget}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.logic.{Environment, FunSpec, FunctionEnv, PredicateEnv, Preprocessor, Program}
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.synthesis.{SynConfig, SynthesisException, SynthesisRunner}
import org.tygus.suslik.util.SynStats
import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.certification.targets.vst.translation.Translation

object VST extends CertificationTarget {
  override val name: String = "VST"
  override val suffix: String = ".v"



  override def certify(proc: Statements.Procedure, env: Environment): Certificate = {
    // retrieve the search tree
    val root =
      CertTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))


    val builder = new StringBuilder
    // append the coq prelude
    val fun_name : String = proc.f.name
    //builder.append(coq_prelude(fun_name))


    Translation.translate(root, proc, env)

  }

  def main(args: Array[String]) : Unit = {
    val certDest = "/tmp/cert-test"
    val certTarget = VST
    val parser = new SSLParser

    val res = parser.parseGoalSYN(
      "{ x :-> a ** y :-> b }  void swap(loc x, loc y)  { x :-> b ** y :-> a }"
    )
    val prog = res.get

    val (specs, predEnv, funcEnv, body) =
      Preprocessor.preprocessProgram(prog, new SynConfig)

    val spec = specs.head

    val config = (new SynConfig).copy(certTarget = VST)

    val env = Environment(predEnv, funcEnv, config, new SynStats(120000))

    val synthesizer = SynthesisRunner.createSynthesizer(env)
    val sresult = synthesizer.synthesizeProc(spec, env, body)

    sresult._1 match {
      case Nil => throw SynthesisException(s"Failed to synthesize:\n$sresult")

      case procs =>

        val targetName = certTarget.name

        val certificate = certTarget.certify(procs.head, env)

        certificate.outputs.foreach({
          case CertificateOutput(filename, name, body) =>
            println(s"synthesized:\n${body}")
        })
   }

  }


}

