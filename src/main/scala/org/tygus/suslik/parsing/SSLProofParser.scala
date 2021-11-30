package org.tygus.suslik.parsing

import org.tygus.suslik.LanguageUtils.{cardinalityPrefix, getTotallyFreshName}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.synthesis.rules.FixedRules

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

class SSLProofParser extends SSLParser {
  override val lexical = new SSLProofLexical

  def ruleParser : Parser[FixedRules] =
    ("done" ^^ ( _ => FixedRules.Emp))

  def parseProof : Parser[List[FixedRules]] =
    repsep(ruleParser, ";" ^^ (_ => ()))

  def parseProof (input: String) :ParseResult[List[FixedRules]] = parse(parseProof)(input)
}

