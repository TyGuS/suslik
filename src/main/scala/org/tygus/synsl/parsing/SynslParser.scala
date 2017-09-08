package org.tygus.synsl.parsing

import org.tygus.synsl.language._
import org.tygus.synsl.logic.Specifications._
import org.tygus.synsl.language.Expressions._

import scala.util.parsing.combinator.syntactical.StandardTokenParsers


class SynslParser extends StandardTokenParsers {

  override val lexical = new SynslLexical

  def primitiveType: Parser[PrimitiveType] =
    "int" ^^^ IntType |||
        "bool" ^^^ BoolType |||
        "void" ^^^ VoidType

  def tpeParser: Parser[SynslType] =
    primitiveType <~ "*" ^^ {
      PtrType(_)
    } ||| primitiveType

  def formal: Parser[(SynslType, Var)] = tpeParser ~ ident ^^ { case a ~ b => (a, Var(b)) }

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

  def parenPhi: Parser[PFormula] = "(" ~> phi <~ ")"

  def phi: Parser[PFormula] = (
      "true" ^^^ PTrue
          ||| "false" ^^^ PFalse
          ||| (literal <~ "<=") ~ literal ^^ { case a ~ b => PLeq(a, b) }
          ||| (literal <~ "<") ~ literal ^^ { case a ~ b => PLtn(a, b) }
          ||| (literal <~ "==") ~ literal ^^ { case a ~ b => PEq(a, b) }
          ||| (parenPhi <~ "/\\") ~ parenPhi ^^ { case a ~ b => PAnd(a, b) }
          ||| (parenPhi <~ "\\/") ~ parenPhi ^^ { case a ~ b => POr(a, b) }
          ||| "not" ~> parenPhi ^^ PNeg
      )

  def simpleSigma: Parser[SFormula] = (
      "emp" ^^^ Emp
          ||| "true" ^^^ STrue
          ||| "false" ^^^ SFalse
          ||| (ident <~ ":->") ~ expr ^^ { case a ~ b => PointsTo(a, 0, b) }
      )

  def sigma: Parser[SFormula] =
    simpleSigma |||
        rep1sep(simpleSigma, "**") ^^ { ss => ss.tail.foldLeft(ss.head)((x, y) => Sep(x, y)) }

  def assertion: Parser[Assertion] = "{" ~> (opt(phi <~ ";") ~ sigma) <~ "}" ^^ {
    case Some(p) ~ s => Assertion(p, s)
    case None ~ s => Assertion(PTrue, s)
  }

  def spec: Parser[FullSpec] = assertion ~ tpeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ assertion ^^ {
    case pre ~ tpe ~ name ~ gamma ~ post => FullSpec(Spec(pre, post, gamma), tpe, Some(name))
  }

  def parse(input: String): ParseResult[FullSpec] = spec(new lexical.Scanner(input)) match {
    case e: Error => Failure(e.msg, e.next)
    case Success(_, in) if !in.atEnd => Failure("Non fully parsed", in)
    case s => s
  }

}
