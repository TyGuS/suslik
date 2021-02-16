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

    Translation.translate(root, proc, env)

  }

}

