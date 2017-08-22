package org.tygus.synsl.parsing

import org.tygus.synsl.language.{BoolType, CLang, IntType, PrimitiveType}
import org.tygus.synsl.logic.Specifications

import scala.util.parsing.combinator.syntactical.StandardTokenParsers


class SynslParser extends StandardTokenParsers with Specifications with CLang {

  override val lexical = new SynslLexical

  def primitiveTypeParser: Parser[PrimitiveType] = "int" ^^^ IntType ||| "bool" ^^^ BoolType

  def formal: Parser[(PrimitiveType, Var)] = primitiveTypeParser ~ ident ^^ { case a ~ b => (a, Var(b)) }

  def intLiteral: Parser[PConst] =
    numericLit ^^ (x => PConst(Integer.parseInt(x)))

  def boolLiteral: Parser[PConst] =
    ("true" | "false") ^^ (b => PConst(java.lang.Boolean.parseBoolean(b)))

  def varParser: Parser[Var] = ident ^^ Var

  def parenExpr: Parser[Expr] = "(" ~> expr <~ ")"

  def literal: Parser[Expr] = intLiteral ||| boolLiteral ||| varParser ||| parenExpr

  def expr: Parser[Expr] = (
      literal ~ ("+" ~> literal) ^^ { case a ~ b => EPlus(a, b) }
          ||| literal ~ ("-" ~> literal) ^^ { case a ~ b => EMinus(a, b) }
          ||| literal ~ ("<=" ~> literal) ^^ { case a ~ b => ELeq(a, b) }
          ||| literal ~ ("<" ~> literal) ^^ { case a ~ b => ELtn(a, b) }
          ||| literal ~ ("==" ~> literal) ^^ { case a ~ b => EEq(a, b) }
          ||| literal ~ ("||" ~> literal) ^^ { case a ~ b => EOr(a, b) }
          ||| literal ~ ("&&" ~> literal) ^^ { case a ~ b => EAnd(a, b) }
          ||| "not" ~> literal ^^ ENeg
          ||| literal
      )

  // Formulas

  def parenPhi: Parser[PureFormula] = "(" ~> phi <~ ")"

  def phi: Parser[PureFormula] = (
      "true" ^^^ PTrue
          ||| "false" ^^^ PFalse
          ||| (literal <~ "<=") ~ literal ^^ { case a ~ b => PLeq(a, b) }
          ||| (literal <~ "<") ~ literal ^^ { case a ~ b => PLtn(a, b) }
          ||| (literal <~ "==") ~ literal ^^ { case a ~ b => PEq(a, b) }
          ||| (parenPhi <~ "/\\") ~ parenPhi ^^ { case a ~ b => PAnd(a, b) }
          ||| (parenPhi <~ "\\/") ~ parenPhi ^^ { case a ~ b => POr(a, b) }
          ||| "not" ~> parenPhi ^^ PNeg
      )

  def simpleSigma: Parser[SpatialFormula] = (
      "emp" ^^^ Emp
          ||| "true" ^^^ STrue
          ||| "false" ^^^ SFalse
          ||| (ident <~ ":->") ~ expr ^^ { case a ~ b => PointsTo(a, 0, b) }
      )

  def sigma: Parser[SpatialFormula] =
    simpleSigma |||
        rep1sep(simpleSigma, "**") ^^ { ss => ss.tail.foldLeft(ss.head)((x, y) => Sep(x, y)) }

  def assertion: Parser[Assertion] = "{" ~> (opt(phi <~ ";") ~ sigma) <~ "}" ^^ {
    case Some(p) ~ s => Assertion(p, s)
    case None ~ s => Assertion(PTrue, s)
  }

  def spec: Parser[Spec] = assertion ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ assertion ^^ {
    case pre ~ name ~ formals ~ post => Spec(pre, post, name, formals)
  }

  def parse(input: String): ParseResult[Spec] = spec(new lexical.Scanner(input)) match {
    case e: Error => Failure(e.msg, e.next)
    case Success(_, in) if !in.atEnd => Failure("Non fully parsed", in)
    case s => s
  }

}
