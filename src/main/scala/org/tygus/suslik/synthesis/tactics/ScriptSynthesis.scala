package org.tygus.suslik.synthesis.tactics

import java.io.File

import org.tygus.suslik.parsing.SSLProofParser
import org.tygus.suslik.synthesis.{SearchTree, SynConfig, SynthesisException}
import org.tygus.suslik.synthesis.rules.{FixedRules, Rules}

import scala.io.Source

case class ScriptSynthesis(script: List[FixedRules]) extends Tactic {
  var rule_stream : Iterator[FixedRules] = FixedRules.to_iterator(script)

  override def nextRules(node: SearchTree.OrNode): List[Rules.SynthesisRule] = {
    if (rule_stream.hasNext) {
      val rule = rule_stream.next()
      List(rule)
    } else {
      List()
    }

  }

  override def filterExpansions(allExpansions: Seq[Rules.RuleResult]): Seq[Rules.RuleResult] =
    allExpansions
}
object ScriptSynthesis {
  def buildFromFile(scriptFile: File): ScriptSynthesis = {
    val allLines = Source.fromFile(scriptFile).getLines().toList.mkString("\n")
    val parser = new SSLProofParser
    val res = parser.parseProof(allLines)
    if (!res.successful) {
      throw SynthesisException("Could not parse proof")
    }
    println(res.get)
    ScriptSynthesis(res.get)
  }
}