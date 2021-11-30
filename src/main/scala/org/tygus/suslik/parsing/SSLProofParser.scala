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
import scala.collection.immutable.SortedSet
import scala.collection.mutable.ListBuffer
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

class SSLProofParser extends SSLParser {
  override val lexical = new SSLProofLexical

  def starPartialArgParser: Parser[(String,String)] =
    (ident ~ ("!=" ~> ident)) ^^ {
      case (v1 ~ v2) => (v1,v2)
    }

  def starPartialArgsParser : Parser[List[(String,String)]] =
    "(" ~>  repsep(starPartialArgParser, "," ^^ (_ => ())) <~ ")"

  def nilNotLvalArgsParser : Parser[List[String]] =
    "(" ~>  repsep(ident, "," ^^ (_ => ())) <~ ")"

  def readGhostArgParser : Parser[(String,String,String,Int)] =
    (ident ~ ("->" ~> ident) ~ ("," ~> ident) ~ ("," ~> numericLit ^^ (x => Integer.parseInt(x)))) ^^
    {case ghostVar ~ intoVar ~ fromVar ~ offset => (intoVar,ghostVar,fromVar,offset)}

  def readGhostArgsParser : Parser[(String, String,String, Int)] =
    "(" ~>  readGhostArgParser <~ ")"

  def frameArgsParser : Parser[List[Heaplet]] =
    "(" ~> repsep(heaplet, ",") <~ ")"

  def substLArgParser : Parser[(String,Expr)] =
    ident ~ ("->" ~> expr) ^^ {case (fromVar ~ toExpr) => (fromVar,toExpr)}

  def substLArgsParser : Parser[(String,Expr)] =
    "(" ~> substLArgParser <~ ")"

  def writeArgParser : Parser[(String,Int,Expr)] =
    (ident ~ ("," ~> numericLit ^^ (x => Integer.parseInt(x))) ~ ("," ~> expr)) ^^
      {case intoVar ~ offset ~ expr => (intoVar,offset,expr)}

  def writeArgsParser : Parser[(String,Int,Expr)] =
    "(" ~> writeArgParser <~ ")"

  def checkPostArgsParser : Parser[List[Expr]] =
   "(" ~> repsep(expr, ",") <~ ")"

  def ruleParser : Parser[FixedRules] =
    (("Emp" ^^ ( _ => FixedRules.Emp))
    | ("HaltAndPrintGoal" ^^ (_ => FixedRules.PrintGoal))
    | ("StarPartial" ~> starPartialArgsParser ^^ (args => FixedRules.StarPartial(args)))
    | ("NilNotLval" ~> nilNotLvalArgsParser ^^ (args => FixedRules.NilNotLval(args)))
    | ("Read" ~> readGhostArgsParser ^^ {case (intoVar,ghostVar,fromVar,offset) => FixedRules.ReadGhost(ghostVar,intoVar,fromVar,offset)})
    | ("Frame" ~> frameArgsParser ^^ (args => FixedRules.Frame(args)))
    | ("SubstL" ~> substLArgsParser ^^ {case (fromVar, toExpr) => FixedRules.SubstL(fromVar,toExpr)})
    | ("SubstR" ~> substLArgsParser ^^ {case (fromVar, toExpr) => FixedRules.SubstR(fromVar,toExpr)})
    | ("Write" ~> writeArgsParser ^^ {case (intoVar,offset,expr) => FixedRules.Write(intoVar,offset,expr)})
    | ("CheckPost" ~> checkPostArgsParser ^^ (args => FixedRules.CheckPost(new PFormula(args.to[SortedSet]))))
    )

  def tmpParser (txt:String) : ParseResult[(String,String,String,Int)] = parse(readGhostArgsParser)(txt)

  def parseProof : Parser[List[FixedRules]] =
    repsep(ruleParser, ";")

  def parseProof (input: String) :ParseResult[List[FixedRules]] = parse(parseProof)(input)
}

