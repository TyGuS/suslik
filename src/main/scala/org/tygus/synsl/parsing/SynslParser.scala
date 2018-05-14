package org.tygus.synsl.parsing

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language._
import org.tygus.synsl.logic._

import scala.util.parsing.combinator.syntactical.StandardTokenParsers


class SynslParser extends StandardTokenParsers {

  override val lexical = new SynslLexical

  def tpeParser: Parser[SynslType] =
    "int" ^^^ IntType ||| "bool" ^^^ BoolType ||| "loc" ^^^ LocType ||| "void" ^^^ VoidType

  def formal: Parser[(SynslType, Var)] = tpeParser ~ ident ^^ { case a ~ b => (a, Var(b)) }

  def intLiteral: Parser[PConst] =
    numericLit ^^ (x => IntConst(Integer.parseInt(x)))

  def boolLiteral: Parser[PConst] =
    ("true" | "false") ^^ (b => BoolConst(java.lang.Boolean.parseBoolean(b)))

  def varParser: Parser[Var] = ident ^^ Var

  def parenExpr: Parser[Expr] = "(" ~> expr <~ ")"

  def expLiteral: Parser[Expr] = intLiteral ||| boolLiteral ||| varParser

  def unOpParser: Parser[UnOp] =
    "not" ^^^ OpNot

  def binOpParser: Parser[BinOp] =
    "+" ^^^ OpPlus ||| "-" ^^^ OpMinus ||| "<=" ^^^ OpLeq ||| "<" ^^^ OpLt |||
      "==" ^^^ OpEq ||| "||" ^^^ OpOr ||| "&&" ^^^ OpAnd

  def expr: Parser[Expr] = (
    (expLiteral ~ binOpParser ~ expLiteral) ^^ { case a ~ op ~ b => BinaryExpr(op, a, b) }
      ||| unOpParser ~ expLiteral ^^ { case op ~ a => UnaryExpr(op, a) }
      ||| expLiteral
    )

  // Formulas

  def logLiteral: Parser[PFormula] = "true" ^^^ PTrue ||| "false" ^^^ PFalse

  def parenPhi: Parser[PFormula] = logLiteral ||| "(" ~> phi <~ ")"

  def phi: Parser[PFormula] = (
    logLiteral
      ||| (expLiteral <~ "<=") ~ expLiteral ^^ { case a ~ b => PLeq(a, b) }
      ||| (expLiteral <~ "<") ~ expLiteral ^^ { case a ~ b => PLtn(a, b) }
      ||| (expLiteral <~ "==") ~ expLiteral ^^ { case a ~ b => PEq(a, b) }
      ||| (parenPhi <~ "/\\") ~ parenPhi ^^ { case a ~ b => PAnd(a, b) }
      ||| (parenPhi <~ "\\/") ~ parenPhi ^^ { case a ~ b => POr(a, b) }
      ||| "not" ~> parenPhi ^^ PNeg
    )

  def identWithOffset: Parser[(Ident, Int)] = {
    val ov = ident ~ opt("+" ~> numericLit)
    ("(" ~> ov <~ ")" | ov) ^^ { case i ~ o =>
      val off = Math.max(Integer.parseInt(o.getOrElse("0")), 0)
      (i, off)
    }
  }

  def heaplet: Parser[Heaplet] = (
    (identWithOffset <~ ":->") ~ expr ^^ { case (a, o) ~ b => PointsTo(Var(a), o, b) }
      ||| "[" ~> (ident ~ ("," ~> numericLit)) <~ "]" ^^ { case a ~ s => Block(Var(a), Integer.parseInt(s)) }
      ||| ident ~ ("(" ~> rep1sep(expr, ",") <~ ")") ^^ { case name ~ args => SApp(name, args) }
    )

  def sigma: Parser[SFormula] = (
    "emp" ^^^ SFormula(Nil)
      ||| repsep(heaplet, "**") ^^ { hs => SFormula(hs) }
    )

  def assertion: Parser[Assertion] = "{" ~> (opt(phi <~ ";") ~ sigma) <~ "}" ^^ {
    case Some(p) ~ s => Assertion(p, s)
    case None ~ s => Assertion(PTrue, s)
  }

  def indClause: Parser[InductiveClause] =
    phi ~ ("=>" ~> sigma) ^^ { case p ~ s => InductiveClause(p, s) }

  def indPredicate: Parser[InductivePredicate] =
    ("predicate" ~> ident) ~ ("(" ~> rep1sep(varParser, ",") <~ ")") ~
      (("{" ~ opt("|")) ~> rep1sep(indClause, "|") <~ "}") ^^ {
      case name ~ params ~ clauses => InductivePredicate(name, params, clauses)
    }

  def spec: Parser[Goal] = assertion ~ assertion ~ repsep(formal, ",") ^^ {
    case pre ~ post ~ formals => Goal(pre, post, formals)
  }

  def uGoal: Parser[UnificationGoal] = ("(" ~> rep1sep(varParser, ",") <~ ")") ~ assertion ^^ {
    case params ~ formula => UnificationGoal(formula, params.toSet)
  }

  def goalFunction: Parser[GoalFunction] = assertion ~ tpeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ assertion ^^ {
    case pre ~ tpe ~ name ~ formals ~ post => GoalFunction(name, Goal(pre, post, formals), tpe)
  }

  def program: Parser[Program] = rep(indPredicate ||| goalFunction) ^^ Program

  def parse[T](p: Parser[T])(input: String): ParseResult[T] = p(new lexical.Scanner(input)) match {
    case e: Error => Failure(e.msg, e.next)
    case Success(_, in) if !in.atEnd => Failure("Not fully parsed", in)
    case s => s
  }

  def parseSpec(input: String): ParseResult[Goal] = parse(spec)(input)

  def parseUnificationGoal(input: String): ParseResult[UnificationGoal] = parse(uGoal)(input)

  def parseGoal(input: String): ParseResult[Program] = parse(program)(input)
}
