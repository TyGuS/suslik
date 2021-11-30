package org.tygus.suslik.synthesis.tactics

import java.io.File

import org.tygus.suslik.parsing.SSLProofParser
import org.tygus.suslik.synthesis.{SearchTree, SynConfig, SynthesisException}
import org.tygus.suslik.synthesis.rules.{FixedRules, Rules}

import scala.io.Source

case class ScriptSynthesis(script: List[FixedRules]) extends Tactic {
  var rule_stream : List[FixedRules] = FixedRules.to_iterator(script).toList

  override def nextRules(node: SearchTree.OrNode): List[Rules.SynthesisRule] = {
    rule_stream match {
      case Nil => Nil
      case ::(hd,tl) => {
        rule_stream = tl
        List(hd)
      }
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
    if (!res.successful || res.get.isEmpty) {
      throw SynthesisException(s"Could not parse proof ${res}")
    }
    println(res.get)
    ScriptSynthesis(res.get)
  }
}