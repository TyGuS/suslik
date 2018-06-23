package org.tygus.synsl.parsing

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language._
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.unification.UnificationGoal

import scala.util.parsing.combinator.syntactical.StandardTokenParsers


class SynslParser extends StandardTokenParsers with SepLogicUtils {

  override val lexical = new SynslLexical

  def typeParser: Parser[SynslType] =
    ("int" ^^^ IntType
        | "bool" ^^^ BoolType
        | "loc" ^^^ LocType
        | "intset" ^^^ IntSetType
        | "void" ^^^ VoidType)

  def formal: Parser[(SynslType, Var)] = typeParser ~ ident ^^ { case a ~ b => (a, Var(b)) }

  def intLiteral: Parser[Const] =
    numericLit ^^ (x => IntConst(Integer.parseInt(x)))

  def boolLiteral: Parser[Const] =
    ("true" | "false") ^^ (b => BoolConst(java.lang.Boolean.parseBoolean(b)))

  def setLiteral: Parser[Expr] =
    "{" ~> repsep(expr, ",") <~ "}" ^^ SetLiteral

  def varParser: Parser[Var] = ident ^^ Var

  def unOpParser: Parser[UnOp] =
    "not" ^^^ OpNot

  def termOpParser: Parser[BinOp] =  "+" ^^^ OpPlus ||| "-" ^^^ OpMinus ||| "++" ^^^ OpUnion

  def relOpParser: Parser[BinOp] = "<=" ^^^ OpLeq ||| "<" ^^^ OpLt ||| "==" ^^^ OpEq ||| "=i" ^^^ OpEq

  def logOpParser: Parser[BinOp] =  "\\/" ^^^ OpOr ||| "/\\" ^^^ OpAnd

  def binOpParser (p: Parser[BinOp]): Parser[(Expr,Expr) => Expr] = {
    p ^^ {op => (l,r) => BinaryExpr(op, l, r)}
  }

  def atom: Parser[Expr] = (
      unOpParser ~ atom ^^ { case op ~ a => UnaryExpr(op, a) }
        | "(" ~> expr <~ ")"
        | intLiteral | boolLiteral | setLiteral
        | varParser
    )

  def term: Parser[Expr] = chainl1(atom, binOpParser(termOpParser))

  def relExpr: Parser[Expr] =
    term ~ opt(relOpParser ~ term) ^^ {
      case a ~ None => a
      case a ~ Some(op ~ b) => BinaryExpr(op, a, b) }

  def expr: Parser[Expr] = chainl1(relExpr, binOpParser (logOpParser))

  // Formulas

  def phi: Parser[PFormula] = {
    for {
      e <- expr
      p = fromExpr(e)
      if p.isDefined
    }  yield p.head
  }

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
    case pre ~ post ~ formals => Goal(pre, post, formals, "foo",
      Derivation(pre.sigma.chunks, post.sigma.chunks))
  }

  def uGoal: Parser[UnificationGoal] = ("(" ~> rep1sep(varParser, ",") <~ ")") ~ assertion ^^ {
    case params ~ formula => UnificationGoal(formula, params.toSet)
  }

  def goalFunction: Parser[FunSpec] = assertion ~ typeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ assertion ^^ {
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
