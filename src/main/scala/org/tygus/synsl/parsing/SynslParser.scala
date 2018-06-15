package org.tygus.synsl.parsing

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language._
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.unification.UnificationGoal

import scala.util.parsing.combinator.syntactical.StandardTokenParsers


class SynslParser extends StandardTokenParsers {

  override val lexical = new SynslLexical

  val tpeParser: Parser[SynslType] =
    ("int" ^^^ IntType
        ||| "bool" ^^^ BoolType
        ||| "loc" ^^^ LocType
        ||| "intset" ^^^ IntSetType
        ||| "void" ^^^ VoidType)

  val formal: Parser[(SynslType, Var)] = tpeParser ~ ident ^^ { case a ~ b => (a, Var(b)) }

  val intLiteral: Parser[Const] =
    numericLit ^^ (x => IntConst(Integer.parseInt(x)))

  val boolLiteral: Parser[Const] =
    ("true" | "false") ^^ (b => BoolConst(java.lang.Boolean.parseBoolean(b)))

  val varParser: Parser[Var] = ident ^^ Var

  val parenExpr: Parser[Expr] = "(" ~> expr <~ ")"

  val expLiteral: Parser[Expr] = intLiteral ||| boolLiteral ||| varParser

  val unOpParser: Parser[UnOp] =
    "not" ^^^ OpNot

  val binOpParser: Parser[BinOp] =
    "+" ^^^ OpPlus ||| "-" ^^^ OpMinus ||| "<=" ^^^ OpLeq ||| "<" ^^^ OpLt |||
        "==" ^^^ OpEq ||| "||" ^^^ OpOr ||| "&&" ^^^ OpAnd

  val expr: Parser[Expr] = (
      (expLiteral ~ binOpParser ~ expLiteral) ^^ { case a ~ op ~ b => BinaryExpr(op, a, b) }
          ||| unOpParser ~ expLiteral ^^ { case op ~ a => UnaryExpr(op, a) }
          ||| expLiteral
      )

  val setExpr: Parser[Expr] =
    ("Empty" ^^^ EmptySet
        ||| "{" ~> expr <~ "}" ^^ SingletonSet
        ||| "Union" ~> ("(" ~> (setExpr ~ ("," ~> setExpr)) <~ ")") ^^ { case l ~ r => SetUnion(l, r) }
        ||| varParser)

  // Formulas

  val logLiteral: Parser[PFormula] = "true" ^^^ PTrue ||| "false" ^^^ PFalse

  val parenPhi: Parser[PFormula] = logLiteral ||| "(" ~> phi <~ ")"

  val phi: Parser[PFormula] = (
      logLiteral
          ||| (expLiteral <~ "<=") ~ expLiteral ^^ { case a ~ b => PLeq(a, b) }
          ||| (expLiteral <~ "<") ~ expLiteral ^^ { case a ~ b => PLtn(a, b) }
          ||| (setExpr <~ "=i") ~ setExpr ^^ { case a ~ b => SEq(a, b) }
          ||| (expLiteral <~ "==") ~ expLiteral ^^ { case a ~ b => PEq(a, b) }
          ||| (parenPhi <~ "/\\") ~ parenPhi ^^ { case a ~ b => PAnd(a, b) }
          ||| (parenPhi <~ "\\/") ~ parenPhi ^^ { case a ~ b => POr(a, b) }
          ||| "not" ~> parenPhi ^^ PNeg
          ||| parenPhi
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
    phi ~ ("=>" ~> assertion) ^^ { case p ~ a => InductiveClause(p, a) }

  def indPredicate: Parser[InductivePredicate] =
    ("predicate" ~> ident) ~ ("(" ~> rep1sep(varParser, ",") <~ ")") ~
        (("{" ~ opt("|")) ~> rep1sep(indClause, "|") <~ "}") ^^ {
      case name ~ params ~ clauses => InductivePredicate(name, params, clauses)
    }

  def spec: Parser[Goal] = assertion ~ assertion ~ repsep(formal, ",") ^^ {
    case pre ~ post ~ formals => Goal(pre, post, formals, "foo", Derivation(pre.sigma.chunks, post.sigma.chunks))
  }

  def uGoal: Parser[UnificationGoal] = ("(" ~> rep1sep(varParser, ",") <~ ")") ~ assertion ^^ {
    case params ~ formula => UnificationGoal(formula, params.toSet)
  }

  def goalFunction: Parser[FunSpec] = assertion ~ tpeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ assertion ^^ {
    case pre ~ tpe ~ name ~ formals ~ post => FunSpec(name, tpe, formals, pre, post)
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
